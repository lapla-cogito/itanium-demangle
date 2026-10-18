//! A fast Itanium C++ ABI demangler.

const MAX_DEPTH: u32 = 128;
/// Absent `Sym::suffix` or `Sym::group`.
const NO_DECL: u32 = u32::MAX;

#[derive(Debug)]
pub struct Demangler {
    buf: Vec<u8>,
    /// Scratch for rearranging a name. Cleared between uses.
    scratch: Vec<u8>,
    subs: Vec<Sym>,
    /// Type text moved out of `buf` so a declarator can be edited.
    side: Vec<u8>,
    /// Only the first `template_levels` lists are live.
    template_params: Vec<Vec<Sym>>,
    template_levels: usize,
    depth: u32,
    /// Inside `J...E`, so a pack expansion does not print another `...`.
    in_arg_pack: bool,
    /// Inside a lambda signature. `T_` there is that lambda's `auto`.
    in_lambda_sig: bool,
    /// Local names and expression literals print parameter lists.
    show_params: bool,
    /// `parse_type` depth. A type's template arguments do not open a scope.
    type_depth: u32,
    /// Cv-qualifiers still to print after a parameter list.
    defer_depth: u32,
}

/// Demangle one symbol with a thread-local [`Demangler`].
///
/// `None` means the symbol is not Itanium, or it uses an unimplemented production.
pub fn demangle_owned(symbol: &str) -> Option<String> {
    DEM.with(|cell| {
        let mut demangler = cell.borrow_mut();
        demangler.demangle(symbol).map(str::to_owned)
    })
}

thread_local! {
    static DEM: std::cell::RefCell<Demangler> = std::cell::RefCell::new(Demangler::new());
}

fn is_rust_legacy_symbol(mut symbol: &str) -> bool {
    let llvm = ".llvm.";
    if let Some(i) = symbol.find(llvm) {
        let candidate = &symbol[i + llvm.len()..];
        if candidate
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'A'..=b'F' | b'@'))
        {
            symbol = &symbol[..i];
        }
    }
    let inner = if let Some(rest) = symbol.strip_prefix("_ZN") {
        rest
    } else if let Some(rest) = symbol.strip_prefix("ZN") {
        rest
    } else if let Some(rest) = symbol.strip_prefix("__ZN") {
        rest
    } else {
        return false;
    };
    if inner.bytes().any(|byte| byte & 0x80 != 0) {
        return false;
    }
    let bytes = inner.as_bytes();
    let Some(mut current) = bytes.first().copied() else {
        return false;
    };
    let mut pos = 1;
    while current != b'E' {
        if !current.is_ascii_digit() {
            return false;
        }
        let mut len = 0usize;
        while current.is_ascii_digit() {
            let Some(next) = len
                .checked_mul(10)
                .and_then(|len| len.checked_add((current - b'0') as usize))
            else {
                return false;
            };
            len = next;
            let Some(next) = bytes.get(pos).copied() else {
                return false;
            };
            current = next;
            pos += 1;
        }
        for _ in 0..len {
            let Some(next) = bytes.get(pos).copied() else {
                return false;
            };
            current = next;
            pos += 1;
        }
    }
    let Some(suffix) = bytes.get(pos..) else {
        return false;
    };
    suffix.is_empty() || (suffix[0] == b'.' && suffix.iter().copied().all(is_symbol_byte))
}

fn is_symbol_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric()
        || matches!(byte, 0x21..=0x2F | 0x3A..=0x40 | 0x5B..=0x60 | 0x7B..=0x7E)
}

#[derive(Clone, Copy, Debug)]
struct Sym {
    start: u32,
    end: u32,
    base_start: u32,
    base_end: u32,
    /// Array or function declarator. [`NO_DECL`] if there is none.
    suffix: u32,
    /// `'('` of a pointer or reference group. [`NO_DECL`] if there is none.
    group: u32,
    ends_with_template: bool,
    /// Constructor, destructor, or conversion operator. No return type follows.
    is_ctor: bool,
    cv_const: bool,
    cv_volatile: bool,
    cv_restrict: bool,
    /// `0`, `1` for `&`, or `2` for `&&`.
    ref_qual: u8,
    /// Ranges name bytes in `Demangler::side` rather than the output buffer.
    side: bool,
}

impl Sym {
    fn span(start: u32, end: u32) -> Self {
        Self {
            start,
            end,
            base_start: start,
            base_end: end,
            suffix: NO_DECL,
            group: NO_DECL,
            ends_with_template: false,
            is_ctor: false,
            cv_const: false,
            cv_volatile: false,
            cv_restrict: false,
            ref_qual: 0,
            side: false,
        }
    }

    fn set_end(mut self, new_end: u32) -> Self {
        self.end = new_end;
        self
    }

    fn relocate(self, new_start: u32) -> Self {
        let delta = new_start as i64 - self.start as i64;
        let shift = |idx: u32| {
            if idx == NO_DECL {
                idx
            } else {
                (idx as i64 + delta) as u32
            }
        };
        Self {
            start: new_start,
            end: shift(self.end),
            base_start: shift(self.base_start),
            base_end: shift(self.base_end),
            suffix: shift(self.suffix),
            group: shift(self.group),
            ..self
        }
    }

    /// Rebuild this symbol as a name. Declarator holes are cleared; qualifier flags stay.
    fn as_name(self, start: u32, end: u32, base_start: u32, base_end: u32) -> Self {
        Self {
            start,
            end,
            base_start,
            base_end,
            suffix: NO_DECL,
            group: NO_DECL,
            side: false,
            ..self
        }
    }

    fn with_template(mut self) -> Self {
        self.ends_with_template = true;
        self
    }

    fn clear_qualifiers(mut self) -> Self {
        self.cv_const = false;
        self.cv_volatile = false;
        self.cv_restrict = false;
        self.ref_qual = 0;
        self
    }
}

impl Default for Demangler {
    fn default() -> Self {
        Self::new()
    }
}

impl Demangler {
    pub fn new() -> Self {
        Self {
            buf: Vec::with_capacity(256),
            scratch: Vec::with_capacity(128),
            side: Vec::new(),
            subs: Vec::with_capacity(32),
            template_params: Vec::new(),
            template_levels: 0,
            depth: 0,
            in_arg_pack: false,
            in_lambda_sig: false,
            show_params: false,
            defer_depth: 0,
            type_depth: 0,
        }
    }

    /// Demangle `symbol`.
    ///
    /// The returned string is invalid after the next call.
    pub fn demangle<'a>(&'a mut self, symbol: &'a str) -> Option<&'a str> {
        if is_rust_legacy_symbol(symbol) {
            return None;
        }
        self.buf.clear();
        self.side.clear();
        self.subs.clear();
        self.template_levels = 0;
        self.depth = 0;
        self.in_arg_pack = false;
        self.in_lambda_sig = false;
        self.show_params = false;
        self.defer_depth = 0;
        self.type_depth = 0;

        let input = symbol.as_bytes();
        let pos = if input.starts_with(b"_Z") {
            2
        } else if input.starts_with(b"__Z") {
            3
        } else {
            return None;
        };

        let mut parser = Parser {
            d: self,
            input,
            pos,
        };
        let mut sym = parser.parse_encoding()?;
        if parser.peek() == Some(b'.') {
            sym = parser.d.materialize_tail(sym);
            parser.d.append(&parser.input[parser.pos..]);
            sym.end = parser.d.buf.len() as u32;
        }
        let start = sym.start as usize;
        let end = sym.end as usize;
        std::str::from_utf8(&self.buf[start..end]).ok()
    }

    fn begin_template_level(&mut self) {
        if self.template_levels == self.template_params.len() {
            self.template_params.push(Vec::new());
        } else {
            self.template_params[self.template_levels].clear();
        }
        self.template_levels += 1;
    }

    fn push_template_arg(&mut self, sym: Sym) -> Option<()> {
        self.template_params
            .get_mut(self.template_levels.checked_sub(1)?)?
            .push(sym);
        Some(())
    }

    fn template_arg(&self, index: usize) -> Option<Sym> {
        self.template_params
            .get(self.template_levels.checked_sub(1)?)?
            .get(index)
            .copied()
    }

    fn append(&mut self, bytes: &[u8]) {
        self.buf.extend_from_slice(bytes);
    }

    fn append_scratch(&mut self) -> Sym {
        let start = self.buf.len();
        let extra = self.scratch.len();
        self.buf.resize(start + extra, 0);
        self.buf[start..].copy_from_slice(&self.scratch);
        Sym::span(start as u32, self.buf.len() as u32)
    }

    fn append_range(&mut self, sym: Sym) {
        self.copy_bytes(sym.side, sym.start, sym.end);
    }

    fn append_base(&mut self, sym: Sym) {
        self.copy_bytes(sym.side, sym.base_start, sym.base_end);
    }

    fn copy_bytes(&mut self, side: bool, start: u32, end: u32) {
        if start >= end {
            return;
        }
        if side {
            self.buf
                .extend_from_slice(&self.side[start as usize..end as usize]);
        } else {
            self.buf.extend_from_within(start as usize..end as usize);
        }
    }

    fn sym_bytes(&self, sym: Sym) -> &[u8] {
        let buf = if sym.side { &self.side } else { &self.buf };
        &buf[sym.start as usize..sym.end as usize]
    }

    fn push_str(&mut self, text: &str) -> Sym {
        let start = self.buf.len() as u32;
        self.append(text.as_bytes());
        Sym::span(start, self.buf.len() as u32)
    }

    fn push_well_known(&mut self, text: &str, base_off: u32, base_len: u32) -> Sym {
        let start = self.buf.len() as u32;
        self.append(text.as_bytes());
        let end = self.buf.len() as u32;
        Sym {
            start,
            end,
            base_start: start + base_off,
            base_end: start + base_off + base_len,
            ..Sym::span(start, end)
        }
    }

    fn materialize_tail(&mut self, sym: Sym) -> Sym {
        if !sym.side && sym.end as usize == self.buf.len() {
            return sym;
        }
        self.copy_to_main(sym)
    }

    fn copy_to_main(&mut self, sym: Sym) -> Sym {
        let new_start = self.buf.len() as u32;
        self.append_range(sym);
        let mut copied = sym.relocate(new_start);
        copied.side = false;
        copied
    }

    /// A main-buffer tail that can be edited without rewriting a saved range.
    fn editable(&mut self, sym: Sym) -> Sym {
        if !sym.side
            && sym.end as usize == self.buf.len()
            && !self.overlaps_saved(sym.start, sym.end)
        {
            return sym;
        }
        self.copy_to_main(sym)
    }

    fn append_suffix(&mut self, sym: Sym, suffix: &str) -> Sym {
        let sym = self.materialize_tail(sym);
        self.append(suffix.as_bytes());
        sym.set_end(self.buf.len() as u32)
    }

    fn overlaps_saved(&self, start: u32, end: u32) -> bool {
        let hit = |sym: &Sym| {
            !sym.side
                && ((sym.start < end && sym.end > start)
                    || (sym.base_start < end && sym.base_end > start))
        };
        self.subs.iter().any(hit)
            || self.template_params[..self.template_levels]
                .iter()
                .any(|level| level.iter().any(hit))
    }

    fn qualify(&mut self, scope: Sym, leaf: Sym) -> Sym {
        if scope.end == leaf.start {
            self.insert_at(leaf.start, b"::");
            let base_off = leaf.base_start - leaf.start;
            let base_len = leaf.base_end - leaf.base_start;
            let text_len = leaf.end - leaf.start;
            let leaf_start = leaf.start + 2;
            return leaf.as_name(
                scope.start,
                leaf_start + text_len,
                leaf_start + base_off,
                leaf_start + base_off + base_len,
            );
        }
        // The leaf is already the tail. Rewrite that tail as `scope::leaf`.
        if leaf.end as usize == self.buf.len() {
            let base_off = leaf.base_start - leaf.start;
            let base_len = leaf.base_end - leaf.base_start;
            self.scratch.clear();
            self.scratch
                .extend_from_slice(&self.buf[leaf.start as usize..leaf.end as usize]);
            self.truncate(leaf.start);
            let start = self.buf.len() as u32;
            let scope_len = scope.end - scope.start;
            self.append_range(scope);
            self.append(b"::");
            self.append_scratch();
            return leaf.as_name(
                start,
                self.buf.len() as u32,
                start + scope_len + 2 + base_off,
                start + scope_len + 2 + base_off + base_len,
            );
        }
        let start = self.buf.len() as u32;
        let scope_len = scope.end - scope.start;
        let base_off = leaf.base_start - leaf.start;
        let base_len = leaf.base_end - leaf.base_start;
        self.append_range(scope);
        self.append(b"::");
        self.append_range(leaf);
        leaf.as_name(
            start,
            self.buf.len() as u32,
            start + scope_len + 2 + base_off,
            start + scope_len + 2 + base_off + base_len,
        )
    }

    fn qualify_ctor(&mut self, scope: Sym, destructor: bool) -> Sym {
        let start = self.buf.len() as u32;
        self.append_range(scope);
        self.append(b"::");
        let base_start = self.buf.len() as u32;
        if destructor {
            self.append(b"~");
        }
        self.append_base(scope);
        let end = self.buf.len() as u32;
        Sym {
            start,
            end,
            base_start,
            base_end: end,
            is_ctor: true,
            ..Sym::span(start, end)
        }
    }

    fn attach_template_args(&mut self, name: Sym, args_start: u32, args_end: u32) -> Sym {
        if name.end == args_start {
            if name.end > name.start && self.buf[name.end as usize - 1] == b'<' {
                self.insert_at(args_start, b" ");
                return name
                    .as_name(name.start, args_end + 1, name.base_start, name.base_end)
                    .with_template();
            }
            return name
                .as_name(name.start, args_end, name.base_start, name.base_end)
                .with_template();
        }
        // Arguments were written at the tail. Move them to after `name`.
        self.scratch.clear();
        self.scratch
            .extend_from_slice(&self.buf[args_start as usize..args_end as usize]);
        self.truncate(args_start);
        let start = self.buf.len() as u32;
        let base_off = name.base_start - name.start;
        let base_len = name.base_end - name.base_start;
        self.append_range(name);
        if self.buf.last() == Some(&b'<') {
            self.append(b" ");
        }
        let new_args_start = self.buf.len() as u32;
        self.append_scratch();
        let delta = new_args_start - args_start;
        if delta != 0 {
            self.shift_contained(args_start, args_end, delta);
        }
        name.as_name(
            start,
            self.buf.len() as u32,
            start + base_off,
            start + base_off + base_len,
        )
        .with_template()
    }

    fn format_params(&mut self, name: Sym, params: &[Sym]) -> Sym {
        let start = self.buf.len() as u32;
        let base_off = name.base_start - name.start;
        let base_len = name.base_end - name.base_start;
        let name_copy = self.buf.len() as u32;
        self.append_range(name);
        if !name.side {
            self.retarget(name.start, name.end, name_copy);
        }
        self.append(b"(");
        for (index, param) in params.iter().enumerate() {
            if index > 0 {
                self.append(b", ");
            }
            let new_start = self.buf.len() as u32;
            self.append_range(*param);
            if !param.side {
                self.retarget(param.start, param.end, new_start);
            }
        }
        self.append(b")");
        let mut sym = name.as_name(
            start,
            self.buf.len() as u32,
            start + base_off,
            start + base_off + base_len,
        );
        sym.ends_with_template = false;
        self.apply_name_qualifiers(sym)
    }

    /// `const` is printed only while parameters are shown. Ref-qualifiers always are.
    fn apply_name_qualifiers(&mut self, sym: Sym) -> Sym {
        if !sym.cv_const && !sym.cv_volatile && !sym.cv_restrict && sym.ref_qual == 0 {
            return sym;
        }
        let sym = self.materialize_tail(sym);
        if self.show_params {
            if sym.cv_const {
                self.append(b" const");
            }
            if sym.cv_volatile {
                self.append(b" volatile");
            }
            if sym.cv_restrict {
                self.append(b" restrict");
            }
        }
        match sym.ref_qual {
            1 => self.append(b" &"),
            2 => self.append(b" &&"),
            _ => {}
        }
        sym.as_name(
            sym.start,
            self.buf.len() as u32,
            sym.base_start,
            sym.base_end,
        )
        .clear_qualifiers()
    }

    /// `'*'`, `'&'`, or `'O'` for `&&`.
    fn wrap_pointer(&mut self, inner: Sym, kind: u8) -> Option<Sym> {
        if kind != b'*'
            && let Some(collapsed) = self.collapse_ref(inner, kind == b'O')
        {
            return Some(collapsed);
        }
        let token: &[u8] = match kind {
            b'*' => b"*",
            b'&' => b"&",
            b'O' => b"&&",
            _ => return None,
        };
        if inner.suffix == NO_DECL {
            let sym = self.materialize_tail(inner);
            self.append(token);
            return Some(sym.set_end(self.buf.len() as u32));
        }
        let sym = self.editable(inner);
        if sym.group != NO_DECL {
            let at = find_close(&self.buf, sym.group)?;
            self.insert_at(at, token);
            return Some(shift_local(sym, at, token.len() as u32));
        }
        let at = sym.suffix;
        let needs_space =
            at > 0 && !matches!(self.buf.get(at as usize - 1), Some(b' ' | b'(' | b'*'));
        let mut wrapped = Vec::with_capacity(token.len() + 3);
        if needs_space {
            wrapped.push(b' ');
        }
        wrapped.extend_from_slice(b"(");
        wrapped.extend_from_slice(token);
        wrapped.extend_from_slice(b")");
        self.insert_at(at, &wrapped);
        let mut sym = shift_local(sym, at, wrapped.len() as u32);
        sym.group = at + u32::from(needs_space);
        Some(sym)
    }

    /// `None` when `inner` is not a reference, so the caller appends one.
    fn collapse_ref(&mut self, inner: Sym, rvalue: bool) -> Option<Sym> {
        if inner.suffix != NO_DECL || inner.group != NO_DECL {
            return None;
        }
        let bytes = self.sym_bytes(inner);
        let ends_r = bytes.ends_with(b"&&");
        let ends_ref = ends_r || bytes.ends_with(b"&");
        if !ends_ref {
            return None;
        }
        let sym = self.editable(inner);
        let ends_r = self.sym_bytes(sym).ends_with(b"&&");
        if !rvalue || !ends_r {
            if ends_r {
                self.truncate(sym.end - 1);
                return Some(sym.set_end(sym.end - 1));
            }
            return Some(sym);
        }
        Some(sym)
    }

    fn wrap_cv(&mut self, inner: Sym, text: &str) -> Option<Sym> {
        let editing = inner.group != NO_DECL
            || (inner.suffix != NO_DECL
                && self
                    .sym_bytes(inner)
                    .get((inner.suffix - inner.start) as usize)
                    == Some(&b' '));
        let sym = if editing {
            self.editable(inner)
        } else {
            self.materialize_tail(inner)
        };
        if sym.group != NO_DECL {
            let close = find_close(&self.buf, sym.group)?;
            self.insert_at(close, text.as_bytes());
            return Some(shift_local(sym, close, text.len() as u32));
        }
        if sym.suffix != NO_DECL && self.buf.get(sym.suffix as usize) == Some(&b' ') {
            self.insert_at(sym.suffix, text.as_bytes());
            return Some(shift_local(sym, sym.suffix, text.len() as u32));
        }
        self.append(text.as_bytes());
        Some(sym.set_end(self.buf.len() as u32))
    }

    fn wrap_member_pointer(&mut self, class_ty: Sym, member: Sym) -> Option<Sym> {
        let mut token = Vec::with_capacity((class_ty.end - class_ty.start) as usize + 3);
        token.extend_from_slice(self.sym_bytes(class_ty));
        token.extend_from_slice(b"::*");
        let member = self.editable(member);
        if member.suffix != NO_DECL && self.buf.get(member.suffix as usize) == Some(&b'(') {
            let at = member.suffix;
            let needs_space =
                at > 0 && !matches!(self.buf.get(at as usize - 1), Some(b' ' | b'(' | b'*'));
            let mut wrapped = Vec::with_capacity(token.len() + 3);
            if needs_space {
                wrapped.push(b' ');
            }
            wrapped.push(b'(');
            wrapped.extend_from_slice(&token);
            wrapped.push(b')');
            self.insert_at(at, &wrapped);
            let mut sym = shift_local(member, at, wrapped.len() as u32);
            sym.group = at + u32::from(needs_space);
            return Some(sym);
        }
        if member.suffix != NO_DECL || member.group != NO_DECL {
            return None;
        }
        let member = self.materialize_tail(member);
        if !matches!(self.buf.last(), Some(b'(' | b' ')) {
            self.append(b" ");
        }
        self.append(&token);
        Some(member.set_end(self.buf.len() as u32))
    }

    fn wrap_array(&mut self, elem: Sym, dim: Option<usize>) -> Option<Sym> {
        let editing = elem.group != NO_DECL || elem.suffix != NO_DECL;
        let sym = if editing {
            self.editable(elem)
        } else {
            self.materialize_tail(elem)
        };
        if sym.group != NO_DECL {
            let close = find_close(&self.buf, sym.group)?;
            let dim_text = render_dim(dim, true);
            self.insert_at(close, &dim_text);
            return Some(shift_local(sym, close, dim_text.len() as u32));
        }
        if sym.suffix != NO_DECL && self.buf.get(sym.suffix as usize) == Some(&b' ') {
            let at = sym.suffix + 1;
            let dim_text = render_dim(dim, false);
            self.insert_at(at, &dim_text);
            return Some(shift_local(sym, at, dim_text.len() as u32));
        }
        if sym.suffix != NO_DECL {
            return None;
        }
        let dim_text = render_dim(dim, true);
        let suffix = self.buf.len() as u32;
        self.append(&dim_text);
        let mut sym = sym.set_end(self.buf.len() as u32);
        sym.suffix = suffix;
        Some(sym)
    }

    fn glue(&mut self, parts: &[Glue<'_>]) -> Option<Sym> {
        let start = self.buf.len() as u32;
        for part in parts {
            match part {
                Glue::Text(text) => self.append(text),
                Glue::Sym(sym) => self.append_range(*sym),
            }
        }
        Some(Sym::span(start, self.buf.len() as u32))
    }

    /// Point substitutions that referred to `[from, to)` at the copy now starting at `new_start`.
    fn retarget(&mut self, from: u32, to: u32, new_start: u32) {
        let delta = new_start as i64 - from as i64;
        if delta == 0 {
            return;
        }
        let shift = |sym: &mut Sym| {
            if !sym.side && sym.start >= from && sym.end <= to {
                let shifted = sym.relocate((sym.start as i64 + delta) as u32);
                *sym = shifted;
            }
        };
        for sym in &mut self.subs {
            shift(sym);
        }
        for level in &mut self.template_params[..self.template_levels] {
            for sym in level {
                shift(sym);
            }
        }
    }

    /// Make `sym` occupy `[cursor, ...)`, dropping bytes that were written before it.
    ///
    /// Returns `None` when a substitution still points at those bytes.
    fn place_at_cursor(&mut self, sym: Sym, cursor: u32) -> Option<Sym> {
        if !sym.side && sym.start == cursor {
            return Some(sym);
        }
        if sym.end as usize != self.buf.len() {
            if cursor as usize != self.buf.len() {
                return None;
            }
            return Some(self.copy_to_main(sym));
        }
        let junk_end = sym.start;
        self.evict_junk(cursor, junk_end)?;
        self.scratch.clear();
        self.scratch
            .extend_from_slice(&self.buf[sym.start as usize..sym.end as usize]);
        let old_start = sym.start;
        let old_end = sym.end;
        self.truncate(cursor);
        let new_start = self.buf.len() as u32;
        self.append_scratch();
        self.retarget(old_start, old_end, new_start);
        Some(sym.relocate(new_start))
    }

    /// Move ranges that lay entirely inside `[from, to)` by `delta`.
    fn shift_contained(&mut self, from: u32, to: u32, delta: u32) {
        let shift = |sym: &mut Sym| {
            if !sym.side && sym.start >= from && sym.end <= to {
                *sym = sym.relocate(sym.start + delta);
            }
        };
        for sym in &mut self.subs {
            shift(sym);
        }
        for level in &mut self.template_params[..self.template_levels] {
            for sym in level {
                shift(sym);
            }
        }
    }

    fn insert_at(&mut self, pos: u32, bytes: &[u8]) {
        let at = pos as usize;
        let old_len = self.buf.len();
        let extra = bytes.len();
        self.buf.resize(old_len + extra, 0);
        self.buf.copy_within(at..old_len, at + extra);
        self.buf[at..at + extra].copy_from_slice(bytes);
        let amount = extra as u32;
        for sym in &mut self.subs {
            if !sym.side {
                shift_sym(sym, pos, amount);
            }
        }
        for level in &mut self.template_params[..self.template_levels] {
            for sym in level {
                if !sym.side {
                    shift_sym(sym, pos, amount);
                }
            }
        }
    }

    /// Keep substitutions that name `[from, to)` by moving that text out of the output buffer.
    fn evict_junk(&mut self, from: u32, to: u32) -> Option<()> {
        if from >= to {
            return Some(());
        }
        let bad = |sym: &Sym| {
            if sym.side {
                return false;
            }
            let overlaps = sym.start < to && sym.end > from;
            let inside = sym.start >= from && sym.end <= to;
            let base_overlaps = sym.base_start < to && sym.base_end > from;
            let base_inside = sym.base_start >= from && sym.base_end <= to;
            (overlaps && !inside) || (base_overlaps && !base_inside)
        };
        if self.subs.iter().any(bad)
            || self.template_params[..self.template_levels]
                .iter()
                .any(|level| level.iter().any(bad))
        {
            return None;
        }
        let new_base = self.side.len() as u32;
        self.side
            .extend_from_slice(&self.buf[from as usize..to as usize]);
        let delta = new_base as i64 - from as i64;
        let shift = |sym: &mut Sym| {
            if sym.side || sym.start < from || sym.end > to {
                return;
            }
            *sym = sym.relocate((sym.start as i64 + delta) as u32);
            sym.side = true;
        };
        for sym in &mut self.subs {
            shift(sym);
        }
        for level in &mut self.template_params[..self.template_levels] {
            for sym in level {
                shift(sym);
            }
        }
        Some(())
    }

    fn truncate(&mut self, pos: u32) {
        self.buf.truncate(pos as usize);
    }

    fn range_eq(&self, sym: Sym, text: &str) -> bool {
        self.sym_bytes(sym) == text.as_bytes()
    }

    fn write_literal(&mut self, ty: Sym, value: &str) -> Option<Sym> {
        let (negative, digits) = value
            .strip_prefix('n')
            .map_or((false, value), |digits| (true, digits));
        if self.range_eq(ty, "bool") && !negative {
            self.truncate(ty.start);
            let word = match digits {
                "0" => "false",
                "1" => "true",
                _ => return None,
            };
            return Some(self.push_str(word));
        }
        if self.range_eq(ty, "std::nullptr_t") {
            self.truncate(ty.start);
            return Some(self.push_str("nullptr"));
        }
        if self.range_eq(ty, "int") {
            self.truncate(ty.start);
            return Some(self.push_number(negative, digits));
        }
        if self.range_eq(ty, "float")
            || self.range_eq(ty, "double")
            || self.range_eq(ty, "long double")
        {
            self.truncate(ty.start);
            if negative {
                self.append(b"-");
            }
            self.append(b"[");
            self.append(digits.as_bytes());
            self.append(b"]");
            return Some(Sym::span(
                self.buf.len() as u32 - digits.len() as u32 - 2 - u32::from(negative),
                self.buf.len() as u32,
            ));
        }
        // `(type)number`. The type text stays addressable for substitutions.
        let ty = if ty.side || ty.end as usize != self.buf.len() {
            self.copy_to_main(ty)
        } else {
            ty
        };
        self.insert_at(ty.start, b"(");
        self.append(b")");
        if negative {
            self.append(b"-");
        }
        self.append(digits.as_bytes());
        Some(Sym::span(ty.start, self.buf.len() as u32))
    }

    fn push_number(&mut self, negative: bool, digits: &str) -> Sym {
        let start = self.buf.len() as u32;
        if negative {
            self.append(b"-");
        }
        self.append(digits.as_bytes());
        Sym::span(start, self.buf.len() as u32)
    }
}

fn shift_sym(sym: &mut Sym, pos: u32, amount: u32) {
    shift_range(&mut sym.start, &mut sym.end, pos, amount);
    shift_range(&mut sym.base_start, &mut sym.base_end, pos, amount);
    shift_index(&mut sym.suffix, pos, amount);
    shift_index(&mut sym.group, pos, amount);
}

fn shift_index(idx: &mut u32, pos: u32, amount: u32) {
    if *idx != NO_DECL && *idx >= pos {
        *idx += amount;
    }
}

fn shift_local(mut sym: Sym, pos: u32, amount: u32) -> Sym {
    shift_sym(&mut sym, pos, amount);
    sym
}

fn find_close(buf: &[u8], open: u32) -> Option<u32> {
    let mut depth = 0i32;
    for (offset, byte) in buf[open as usize..].iter().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(open + offset as u32);
                }
            }
            _ => {}
        }
    }
    None
}

fn render_dim(dim: Option<usize>, leading_space: bool) -> Vec<u8> {
    let mut out = Vec::new();
    if leading_space {
        out.push(b' ');
    }
    out.push(b'[');
    if let Some(number) = dim {
        out.extend(number.to_string().into_bytes());
    }
    out.push(b']');
    out
}

fn operator_symbol(first: u8, second: u8) -> Option<&'static str> {
    Some(match [first, second] {
        [b'n', b'w'] => " new",
        [b'n', b'a'] => " new[]",
        [b'd', b'l'] => " delete",
        [b'd', b'a'] => " delete[]",
        [b'p', b's'] => "+",
        [b'n', b'g'] => "-",
        [b'a', b'd'] => "&",
        [b'd', b'e'] => "*",
        [b'c', b'o'] => "~",
        [b'p', b'l'] => "+",
        [b'm', b'i'] => "-",
        [b'm', b'l'] => "*",
        [b'd', b'v'] => "/",
        [b'r', b'm'] => "%",
        [b'a', b'n'] => "&",
        [b'o', b'r'] => "|",
        [b'e', b'o'] => "^",
        [b'a', b'S'] => "=",
        [b'p', b'L'] => "+=",
        [b'm', b'I'] => "-=",
        [b'm', b'L'] => "*=",
        [b'd', b'V'] => "/=",
        [b'r', b'M'] => "%=",
        [b'a', b'N'] => "&=",
        [b'o', b'R'] => "|=",
        [b'e', b'O'] => "^=",
        [b'l', b's'] => "<<",
        [b'r', b's'] => ">>",
        [b'l', b'S'] => "<<=",
        [b'r', b'S'] => ">>=",
        [b'e', b'q'] => "==",
        [b'n', b'e'] => "!=",
        [b'l', b't'] => "<",
        [b'g', b't'] => ">",
        [b'l', b'e'] => "<=",
        [b'g', b'e'] => ">=",
        [b'n', b't'] => "!",
        [b'a', b'a'] => "&&",
        [b'o', b'o'] => "||",
        [b'p', b'p'] => "++",
        [b'm', b'm'] => "--",
        [b'c', b'm'] => ",",
        [b'p', b'm'] => "->*",
        [b'p', b't'] => "->",
        [b'c', b'l'] => "()",
        [b'i', b'x'] => "[]",
        [b'q', b'u'] => "?:",
        [b's', b's'] => "<=>",
        _ => return None,
    })
}

fn operator_arity(first: u8, second: u8) -> Option<u8> {
    Some(match [first, second] {
        [b'q', b'u'] => 3,
        [b'p', b's']
        | [b'n', b'g']
        | [b'a', b'd']
        | [b'd', b'e']
        | [b'c', b'o']
        | [b'n', b't']
        | [b'p', b'p']
        | [b'm', b'm']
        | [b'd', b'l']
        | [b'd', b'a'] => 1,
        _ if operator_symbol(first, second).is_some() => 2,
        _ => return None,
    })
}

/// Expression forms that are not a plain unary or binary operator.
fn expression_special(first: u8, second: u8) -> bool {
    matches!(
        [first, second],
        [b'c', b'l']
            | [b'c', b'v']
            | [b't', b'l']
            | [b'i', b'l']
            | [b'd', b'c']
            | [b's', b'c']
            | [b'c', b'c']
            | [b'r', b'c']
            | [b't', b'i']
            | [b't', b'e']
            | [b's', b't']
            | [b's', b'z']
            | [b'a', b't']
            | [b'a', b'z']
            | [b'n', b'x']
            | [b's', b'o']
            | [b'd', b't']
            | [b'p', b't']
            | [b'd', b's']
            | [b's', b'Z']
            | [b's', b'P']
            | [b's', b'p']
            | [b't', b'w']
            | [b't', b'r']
            | [b'g', b's']
            | [b'n', b'w']
            | [b'n', b'a']
            | [b'd', b'l']
            | [b'd', b'a']
    )
}

fn shift_range(start: &mut u32, end: &mut u32, pos: u32, amount: u32) {
    if *end <= pos {
        return;
    }
    if *start >= pos {
        *start += amount;
        *end += amount;
    } else {
        *end += amount;
    }
}

struct Expr {
    sym: Sym,
    /// When this expression is a subexpression, wrap it in parentheses.
    paren: bool,
}

enum Glue<'a> {
    Text(&'a [u8]),
    Sym(Sym),
}

struct Parser<'a> {
    d: &'a mut Demangler,
    input: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn enter(&mut self) -> Option<()> {
        if self.d.depth >= MAX_DEPTH {
            return None;
        }
        self.d.depth += 1;
        Some(())
    }

    fn leave(&mut self) {
        self.d.depth -= 1;
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.input.get(self.pos + offset).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let byte = self.peek()?;
        self.pos += 1;
        Some(byte)
    }

    fn eat(&mut self, byte: u8) -> Option<()> {
        if self.peek() == Some(byte) {
            self.pos += 1;
            Some(())
        } else {
            None
        }
    }

    fn starts_with(&self, prefix: &[u8]) -> bool {
        self.input[self.pos..].starts_with(prefix)
    }

    fn parse_number(&mut self) -> Option<usize> {
        let start = self.pos;
        let mut value: usize = 0;
        while matches!(self.peek(), Some(b'0'..=b'9')) {
            value = value
                .checked_mul(10)?
                .checked_add((self.bump()? - b'0') as usize)?;
        }
        if self.pos == start { None } else { Some(value) }
    }

    fn parse_seq_id(&mut self) -> Option<usize> {
        let start = self.pos;
        let mut value: usize = 0;
        loop {
            let digit = match self.peek() {
                Some(b @ b'0'..=b'9') => (b - b'0') as usize,
                Some(b @ b'A'..=b'Z') => (b - b'A') as usize + 10,
                _ => break,
            };
            value = value.checked_mul(36)?.checked_add(digit)?;
            self.pos += 1;
        }
        if self.pos == start { None } else { Some(value) }
    }

    fn parse_source_name(&mut self) -> Option<Sym> {
        let len = self.parse_number()?;
        let end = self.pos.checked_add(len)?;
        if len == 0 || end > self.input.len() {
            return None;
        }
        let from = self.pos;
        self.pos = end;
        // GCC emits `_GLOBAL__N_…` as the source name of an anonymous namespace.
        if self.input[from..end].starts_with(b"_GLOBAL__N") {
            return Some(self.d.push_str("(anonymous namespace)"));
        }
        let start = self.d.buf.len() as u32;
        self.d.buf.extend_from_slice(&self.input[from..end]);
        Some(Sym::span(start, self.d.buf.len() as u32))
    }

    fn parse_encoding(&mut self) -> Option<Sym> {
        match self.peek() {
            Some(b'T' | b'G') => self.parse_special_name(),
            _ => self.parse_name(),
        }
    }

    fn prefixed(&mut self, prefix: &str, parse_name: bool) -> Option<Sym> {
        let start = self.d.buf.len() as u32;
        self.d.append(prefix.as_bytes());
        let child = if parse_name {
            self.parse_name()?
        } else {
            self.parse_type()?
        };
        let expect = start + prefix.len() as u32;
        let child = if child.start == expect {
            child
        } else {
            // A local name is copied to the tail, past this prefix.
            self.d.place_at_cursor(child, expect)?
        };
        Some(Sym::span(start, child.end))
    }

    fn parse_special_name(&mut self) -> Option<Sym> {
        if self.starts_with(b"TV") {
            self.pos += 2;
            return self
                .prefixed("{vtable(", false)
                .map(|sym| self.d.append_suffix(sym, ")}"));
        }
        if self.starts_with(b"TT") {
            self.pos += 2;
            return self
                .prefixed("{vtt(", false)
                .map(|sym| self.d.append_suffix(sym, ")}"));
        }
        if self.starts_with(b"TI") {
            self.pos += 2;
            return self.prefixed("typeinfo for ", false);
        }
        if self.starts_with(b"TS") {
            self.pos += 2;
            return self.prefixed("typeinfo name for ", false);
        }
        if self.starts_with(b"TF") {
            self.pos += 2;
            return self.prefixed("typeinfo fn for ", false);
        }
        if self.starts_with(b"TH") {
            self.pos += 2;
            return self.prefixed("TLS init function for ", true);
        }
        if self.starts_with(b"TW") {
            self.pos += 2;
            return self.prefixed("TLS wrapper function for ", true);
        }
        if self.starts_with(b"GV") {
            self.pos += 2;
            return self.prefixed("guard variable for ", true);
        }
        if self.starts_with(b"GR") {
            self.pos += 2;
            let name = self.parse_name()?;
            let index = if self.eat(b'_').is_some() {
                0
            } else {
                let index = self.parse_seq_id()?.checked_add(1)?;
                self.eat(b'_')?;
                index
            };
            let rendered = format!("reference temporary #{index} for ");
            let start = self.d.buf.len() as u32;
            self.d.append(rendered.as_bytes());
            self.d.append_range(name);
            return Some(Sym::span(start, self.d.buf.len() as u32));
        }
        if self.starts_with(b"TC") {
            self.pos += 2;
            let start = self.d.buf.len() as u32;
            self.d.append(b"construction vtable for ");
            let first = self.parse_type()?;
            if first.end as usize != self.d.buf.len() {
                return None;
            }
            self.d.append(b"-in-");
            let second = self.parse_type()?;
            if second.end as usize != self.d.buf.len() {
                return None;
            }
            return Some(Sym::span(start, self.d.buf.len() as u32));
        }
        if self.starts_with(b"Th") || self.starts_with(b"Tv") {
            self.pos += 1;
            return self.parse_thunk(false);
        }
        if self.starts_with(b"Tc") {
            self.pos += 2;
            return self.parse_thunk(true);
        }
        None
    }

    fn parse_name(&mut self) -> Option<Sym> {
        self.enter()?;
        let parsed = if self.peek() == Some(b'N') {
            self.parse_nested_name()
        } else if self.peek() == Some(b'Z') {
            self.parse_local_name()
        } else {
            // An unscoped name's template arguments are not the encoding's qualifiers.
            let saved = self.d.defer_depth;
            self.d.defer_depth = 0;
            let parsed = self.parse_unscoped_name();
            self.d.defer_depth = saved;
            parsed
        };
        self.leave();
        parsed
    }

    fn parse_unscoped_name(&mut self) -> Option<Sym> {
        let mut is_subst = false;
        let mut name = if self.starts_with(b"St") {
            self.pos += 2;
            let std_sym = self.d.push_str("std");
            self.parse_unqualified(Some(std_sym))?
        } else if self.peek() == Some(b'S') {
            is_subst = true;
            self.parse_substitution()?
        } else {
            self.parse_unqualified(None)?
        };

        if self.peek() == Some(b'I') {
            if !is_subst {
                self.d.subs.push(name);
            }
            let (args_start, args_end) = self.parse_template_args(true)?;
            name = self.d.attach_template_args(name, args_start, args_end);
        } else if is_subst {
            return None;
        }
        Some(name)
    }

    fn parse_nested_name(&mut self) -> Option<Sym> {
        self.eat(b'N')?;
        let defer_this = self.d.defer_depth > 0;
        if defer_this {
            self.d.defer_depth -= 1;
        }
        let mut cv_const = false;
        let mut cv_volatile = false;
        let mut cv_restrict = false;
        let mut ref_qual = 0u8;
        if self.eat(b'H').is_none() {
            if self.eat(b'r').is_some() {
                cv_restrict = true;
            }
            if self.eat(b'V').is_some() {
                cv_volatile = true;
            }
            if self.eat(b'K').is_some() {
                cv_const = true;
            }
            if self.eat(b'R').is_some() {
                ref_qual = 1;
            } else if self.eat(b'O').is_some() {
                ref_qual = 2;
            }
        }

        let mut so_far: Option<Sym> = None;
        let mut pushed_last = false;
        loop {
            if self.eat(b'E').is_some() {
                break;
            }
            match self.peek() {
                Some(b'T') => {
                    if so_far.is_some() {
                        return None;
                    }
                    so_far = Some(self.parse_template_param()?);
                }
                Some(b'I') => {
                    let prefix = so_far?;
                    let (args_start, args_end) = self.parse_template_args(true)?;
                    so_far = Some(self.d.attach_template_args(prefix, args_start, args_end));
                }
                Some(b'D') if matches!(self.peek_at(1), Some(b't' | b'T')) => return None,
                Some(b'S') => {
                    let subst = if self.starts_with(b"St") {
                        self.pos += 2;
                        self.d.push_str("std")
                    } else {
                        self.parse_substitution()?
                    };
                    if so_far.is_some() {
                        return None;
                    }
                    so_far = Some(subst);
                    pushed_last = false;
                    self.eat(b'M');
                    continue;
                }
                _ => {
                    so_far = Some(self.parse_unqualified(so_far)?);
                }
            }
            self.d.subs.push(so_far?);
            pushed_last = true;
            self.eat(b'M');
        }

        if pushed_last {
            self.d.subs.pop()?;
        }
        let mut name = so_far?;
        name.cv_const = cv_const;
        name.cv_volatile = cv_volatile;
        name.cv_restrict = cv_restrict;
        name.ref_qual = ref_qual;
        if defer_this {
            Some(name)
        } else {
            Some(self.d.apply_name_qualifiers(name))
        }
    }

    fn parse_unqualified(&mut self, scope: Option<Sym>) -> Option<Sym> {
        if self.peek() == Some(b'L') && matches!(self.peek_at(1), Some(b'0'..=b'9')) {
            self.pos += 1;
        }

        let mut joined = false;
        let leaf = if matches!(self.peek(), Some(b'1'..=b'9')) {
            joined = if let Some(scope) = scope {
                !scope.side && scope.end as usize == self.d.buf.len()
            } else {
                false
            };
            if joined {
                self.d.append(b"::");
            }
            let name = self.parse_source_name()?;
            let name = self.parse_abi_tags(name)?;
            if joined {
                let scope = scope?;
                name.as_name(scope.start, name.end, name.base_start, name.base_end)
            } else {
                name
            }
        } else if self.starts_with(b"Ut") {
            self.pos += 2;
            let number = if matches!(self.peek(), Some(b'0'..=b'9')) {
                self.parse_number()?
            } else {
                0
            };
            self.eat(b'_')?;
            let index = number.checked_add(1)?;
            let rendered = format!("{{unnamed type#{index}}}");
            let name = self.d.push_str(&rendered);
            self.parse_abi_tags(name)?
        } else if self.starts_with(b"Ul") {
            let name = self.parse_lambda()?;
            self.parse_abi_tags(name)?
        } else if matches!(self.peek(), Some(b'C' | b'D')) {
            let scope = scope?;
            let name = self.parse_ctor_dtor(scope)?;
            return self.parse_abi_tags(name);
        } else if self.looks_like_operator() {
            let name = self.parse_operator_name()?;
            self.parse_abi_tags(name)?
        } else {
            return None;
        };

        if joined {
            return Some(leaf);
        }
        Some(match scope {
            Some(scope) => self.d.qualify(scope, leaf),
            None => leaf,
        })
    }

    fn parse_ctor_dtor(&mut self, scope: Sym) -> Option<Sym> {
        if self.eat(b'C').is_some() {
            if self.eat(b'I').is_some() {
                return None;
            }
            if !matches!(self.bump()?, b'1'..=b'5') {
                return None;
            }
            return Some(self.d.qualify_ctor(scope, false));
        }
        if matches!(self.peek(), Some(b'D'))
            && matches!(self.peek_at(1), Some(b'0' | b'1' | b'2' | b'4' | b'5'))
        {
            self.pos += 2;
            return Some(self.d.qualify_ctor(scope, true));
        }
        None
    }

    fn parse_abi_tags(&mut self, mut name: Sym) -> Option<Sym> {
        while self.peek() == Some(b'B') && matches!(self.peek_at(1), Some(b'0'..=b'9')) {
            self.pos += 1;
            name = self.d.materialize_tail(name);
            self.d.append(b"[abi:");
            let tag = self.parse_source_name()?;
            if tag.end as usize != self.d.buf.len() {
                return None;
            }
            self.d.append(b"]");
            name = name.set_end(self.d.buf.len() as u32);
        }
        Some(name)
    }

    fn parse_template_args(&mut self, tag: bool) -> Option<(u32, u32)> {
        self.enter()?;
        // Argument types must not take the enclosing function's cv-qualifiers.
        let saved = self.d.defer_depth;
        self.d.defer_depth = 0;
        let parsed = self.parse_template_args_inner(tag);
        self.d.defer_depth = saved;
        self.leave();
        parsed
    }

    fn parse_template_args_inner(&mut self, tag: bool) -> Option<(u32, u32)> {
        self.eat(b'I')?;
        // Only the name being encoded opens a template scope.
        let track = tag && self.d.type_depth == 0;
        if track {
            self.d.begin_template_level();
        }
        let base_level = self.d.template_levels;
        let start = self.d.buf.len() as u32;
        self.d.append(b"<");
        let mut first = true;
        while self.eat(b'E').is_none() {
            if self.peek() == Some(b'Q') {
                return None;
            }
            if !first {
                self.d.append(b", ");
            }
            first = false;
            let cursor = self.d.buf.len() as u32;
            let arg = self.parse_template_arg()?;
            let arg = self.d.place_at_cursor(arg, cursor)?;
            // Drop scopes opened while parsing this argument.
            self.d.template_levels = base_level;
            if track {
                self.d.push_template_arg(arg)?;
            }
        }
        if self.d.buf.last() == Some(&b'>') {
            self.d.append(b" ");
        }
        self.d.append(b">");
        Some((start, self.d.buf.len() as u32))
    }

    fn parse_template_arg(&mut self) -> Option<Sym> {
        let sym = match self.peek() {
            Some(b'X') => self.parse_expression_template_arg()?,
            Some(b'J') => self.parse_arg_pack()?,
            Some(b'L') => self.parse_expr_primary()?,
            _ => self.parse_type()?,
        };
        Some(self.d.materialize_tail(sym))
    }

    fn parse_arg_pack(&mut self) -> Option<Sym> {
        self.enter()?;
        let parsed = self.parse_arg_pack_inner();
        self.leave();
        parsed
    }

    fn parse_arg_pack_inner(&mut self) -> Option<Sym> {
        self.eat(b'J')?;
        let start = self.d.buf.len() as u32;
        let saved = self.d.in_arg_pack;
        self.d.in_arg_pack = true;
        let mut first = true;
        while self.peek() != Some(b'E') {
            if !first {
                self.d.append(b", ");
            }
            first = false;
            let cursor = self.d.buf.len() as u32;
            let arg = self.parse_template_arg()?;
            let Some(arg) = self.d.place_at_cursor(arg, cursor) else {
                self.d.in_arg_pack = saved;
                return None;
            };
            if arg.end as usize != self.d.buf.len() {
                self.d.in_arg_pack = saved;
                return None;
            }
        }
        self.d.in_arg_pack = saved;
        self.eat(b'E')?;
        Some(Sym::span(start, self.d.buf.len() as u32))
    }

    fn parse_lambda(&mut self) -> Option<Sym> {
        self.pos += 2;
        let start = self.d.buf.len() as u32;
        self.d.append(b"{lambda(");
        let saved_depth = self.d.defer_depth;
        self.d.defer_depth = 0;
        let saved_lambda = self.d.in_lambda_sig;
        self.d.in_lambda_sig = true;
        let params = self.parse_lambda_params();
        self.d.in_lambda_sig = saved_lambda;
        self.d.defer_depth = saved_depth;
        params?;
        let number = if matches!(self.peek(), Some(b'0'..=b'9')) {
            Some(self.parse_number()?)
        } else {
            None
        };
        self.eat(b'_')?;
        // `Ul...E_` is closure #1. An explicit number is that value plus two.
        let index = match number {
            None => 1,
            Some(number) => number.checked_add(2)?,
        };
        let suffix = format!(")#{index}}}");
        self.d.append(suffix.as_bytes());
        Some(Sym::span(start, self.d.buf.len() as u32))
    }

    fn parse_lambda_params(&mut self) -> Option<()> {
        if self.peek() == Some(b'v') && self.peek_at(1) == Some(b'E') {
            self.pos += 1;
        } else {
            let mut first = true;
            while self.peek() != Some(b'E') {
                if !first {
                    self.d.append(b", ");
                }
                first = false;
                let cursor = self.d.buf.len() as u32;
                let ty = self.parse_type()?;
                self.d.place_at_cursor(ty, cursor)?;
            }
        }
        self.eat(b'E')?;
        Some(())
    }

    fn at_encoding_end(&self) -> bool {
        matches!(self.peek(), None | Some(b'E' | b'.' | b'_'))
    }

    /// Parse `<encoding>` and, when it is a function, append its parameter list.
    ///
    /// Used for the enclosing function of a local name. Top-level demangling still
    /// omits parameter lists.
    fn parse_encoding_with_params(&mut self) -> Option<Sym> {
        // This encoding's template parameters stay in scope when the name is used as a type.
        let saved_types = self.d.type_depth;
        self.d.type_depth = 0;
        let parsed = self.parse_encoding_body();
        self.d.type_depth = saved_types;
        parsed
    }

    fn parse_encoding_body(&mut self) -> Option<Sym> {
        if matches!(self.peek(), Some(b'T' | b'G')) {
            return self.parse_special_name();
        }
        self.d.defer_depth += 1;
        let seen = self.d.defer_depth;
        let name = self.parse_name();
        if self.d.defer_depth == seen {
            self.d.defer_depth -= 1;
        }
        let name = name?;
        if self.at_encoding_end() {
            return Some(self.d.apply_name_qualifiers(name));
        }
        if name.ends_with_template && !name.is_ctor {
            let saved = self.d.defer_depth;
            self.d.defer_depth = 0;
            let ty = self.parse_type();
            self.d.defer_depth = saved;
            ty?;
            if self.at_encoding_end() {
                return Some(self.d.apply_name_qualifiers(name));
            }
        }
        let saved = self.d.defer_depth;
        self.d.defer_depth = 0;
        let mut params = Vec::new();
        let parsed_params = if self.peek() == Some(b'v')
            && matches!(self.peek_at(1), None | Some(b'E' | b'.' | b'_'))
        {
            self.pos += 1;
            Some(())
        } else {
            let mut ok = Some(());
            while !self.at_encoding_end() {
                match self.parse_type() {
                    Some(ty) => params.push(ty),
                    None => {
                        ok = None;
                        break;
                    }
                }
            }
            ok
        };
        self.d.defer_depth = saved;
        parsed_params?;
        Some(self.d.format_params(name, &params))
    }

    fn parse_local_name(&mut self) -> Option<Sym> {
        self.eat(b'Z')?;
        let saved = self.d.show_params;
        self.d.show_params = true;
        let parsed = self.parse_local_name_body();
        self.d.show_params = saved;
        parsed
    }

    fn parse_local_name_body(&mut self) -> Option<Sym> {
        let encoding = self.parse_encoding_with_params()?;
        self.eat(b'E')?;
        if self.eat(b's').is_some() {
            let encoding = self.d.materialize_tail(encoding);
            return Some(self.d.append_suffix(encoding, "::string literal"));
        }
        if self.peek() == Some(b'd') && matches!(self.peek_at(1), Some(b'_' | b'0'..=b'9')) {
            self.pos += 1;
            if matches!(self.peek(), Some(b'0'..=b'9')) {
                self.parse_number()?;
            }
            self.eat(b'_')?;
            self.parse_name()?;
            return Some(encoding);
        }
        let entity = self.parse_name()?;
        Some(self.d.qualify(encoding, entity))
    }

    fn parse_expr_primary(&mut self) -> Option<Sym> {
        self.eat(b'L')?;
        if self.peek() == Some(b'_') {
            if self.peek_at(1) != Some(b'Z') {
                return None;
            }
            self.pos += 2;
            let saved = self.d.show_params;
            self.d.show_params = true;
            let parsed = self.parse_encoding_with_params();
            self.d.show_params = saved;
            let sym = parsed?;
            self.eat(b'E')?;
            return Some(sym);
        }
        if self.peek() == Some(b'Z') {
            return None;
        }
        let ty = self.parse_type()?;
        if self.peek() == Some(b'E') && self.d.range_eq(ty, "std::nullptr_t") {
            self.pos += 1;
            self.d.truncate(ty.start);
            return Some(self.d.push_str("nullptr"));
        }
        let start = self.pos;
        while self.peek().is_some_and(|byte| byte != b'E') {
            self.pos += 1;
        }
        let value = std::str::from_utf8(&self.input[start..self.pos]).ok()?;
        self.eat(b'E')?;
        self.d.write_literal(ty, value)
    }

    fn parse_template_param(&mut self) -> Option<Sym> {
        self.eat(b'T')?;
        if self.eat(b'L').is_some() {
            return None;
        }
        let index = if self.eat(b'_').is_some() {
            0
        } else {
            let index = self.parse_number()?.checked_add(1)?;
            self.eat(b'_')?;
            index
        };
        // Itanium mangles `auto` in a lambda parameter list as a template parameter.
        if self.d.in_lambda_sig {
            return Some(self.d.push_str("auto"));
        }
        self.d.template_arg(index)
    }

    fn parse_substitution(&mut self) -> Option<Sym> {
        self.eat(b'S')?;
        if matches!(self.peek(), Some(b'a'..=b'z')) {
            let kind = self.bump()?;
            return Some(match kind {
                b'a' => self.d.push_well_known("std::allocator", 5, 9),
                b'b' => self.d.push_well_known("std::basic_string", 5, 12),
                b's' => self.d.push_well_known("std::string", 5, 6),
                b'i' => self.d.push_well_known(
                    "std::basic_istream<char, std::char_traits<char> >",
                    5,
                    13,
                ),
                b'o' => self.d.push_well_known("std::ostream", 5, 7),
                b'd' => self.d.push_well_known(
                    "std::basic_iostream<char, std::char_traits<char> >",
                    5,
                    14,
                ),
                _ => return None,
            });
        }
        let index = if self.eat(b'_').is_some() {
            0
        } else {
            let index = self.parse_seq_id()?.checked_add(1)?;
            self.eat(b'_')?;
            index
        };
        self.d.subs.get(index).copied()
    }

    fn parse_type(&mut self) -> Option<Sym> {
        self.enter()?;
        self.d.type_depth += 1;
        let parsed = self.parse_type_inner();
        self.d.type_depth -= 1;
        self.leave();
        parsed
    }

    fn push_builtin(&mut self, text: &str) -> Sym {
        self.d.push_str(text)
    }

    fn parse_type_inner(&mut self) -> Option<Sym> {
        match self.peek()? {
            b'v' => {
                self.pos += 1;
                Some(self.push_builtin("void"))
            }
            b'w' => {
                self.pos += 1;
                Some(self.push_builtin("wchar_t"))
            }
            b'b' => {
                self.pos += 1;
                Some(self.push_builtin("bool"))
            }
            b'c' => {
                self.pos += 1;
                Some(self.push_builtin("char"))
            }
            b'a' => {
                self.pos += 1;
                Some(self.push_builtin("signed char"))
            }
            b'h' => {
                self.pos += 1;
                Some(self.push_builtin("unsigned char"))
            }
            b's' => {
                self.pos += 1;
                Some(self.push_builtin("short"))
            }
            b't' => {
                self.pos += 1;
                Some(self.push_builtin("unsigned short"))
            }
            b'i' => {
                self.pos += 1;
                Some(self.push_builtin("int"))
            }
            b'j' => {
                self.pos += 1;
                Some(self.push_builtin("unsigned int"))
            }
            b'l' => {
                self.pos += 1;
                Some(self.push_builtin("long"))
            }
            b'm' => {
                self.pos += 1;
                Some(self.push_builtin("unsigned long"))
            }
            b'x' => {
                self.pos += 1;
                Some(self.push_builtin("long long"))
            }
            b'y' => {
                self.pos += 1;
                Some(self.push_builtin("unsigned long long"))
            }
            b'n' => {
                self.pos += 1;
                Some(self.push_builtin("__int128"))
            }
            b'o' => {
                self.pos += 1;
                Some(self.push_builtin("unsigned __int128"))
            }
            b'f' => {
                self.pos += 1;
                Some(self.push_builtin("float"))
            }
            b'd' => {
                self.pos += 1;
                Some(self.push_builtin("double"))
            }
            b'e' => {
                self.pos += 1;
                Some(self.push_builtin("long double"))
            }
            b'g' => {
                self.pos += 1;
                Some(self.push_builtin("__float128"))
            }
            b'z' => {
                self.pos += 1;
                Some(self.push_builtin("..."))
            }
            b'D' if self.peek_at(1) == Some(b'p') => {
                self.pos += 2;
                let inner = self.parse_type()?;
                let sym = if self.d.in_arg_pack {
                    inner
                } else {
                    self.d.append_suffix(inner, "...")
                };
                self.d.subs.push(sym);
                Some(sym)
            }
            b'D' => self.parse_d_type(),
            b'u' => {
                self.pos += 1;
                let name = self.parse_source_name()?;
                if self.peek() == Some(b'I') {
                    return None;
                }
                self.d.subs.push(name);
                Some(name)
            }
            b'A' => {
                let sym = self.parse_array_type()?;
                self.d.subs.push(sym);
                Some(sym)
            }
            b'F' => {
                let sym = self.parse_function_type(false, false, false)?;
                self.d.subs.push(sym);
                Some(sym)
            }
            b'M' => {
                self.pos += 1;
                let class_ty = self.parse_type()?;
                let member = self.parse_type()?;
                let sym = self.d.wrap_member_pointer(class_ty, member)?;
                self.d.subs.push(sym);
                Some(sym)
            }
            b'P' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                let sym = self.d.wrap_pointer(inner, b'*')?;
                self.d.subs.push(sym);
                Some(sym)
            }
            b'R' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                let sym = self.d.wrap_pointer(inner, b'&')?;
                self.d.subs.push(sym);
                Some(sym)
            }
            b'O' => {
                self.pos += 1;
                let inner = self.parse_type()?;
                let sym = self.d.wrap_pointer(inner, b'O')?;
                self.d.subs.push(sym);
                Some(sym)
            }
            b'K' | b'V' | b'r' | b'U' => self.parse_qualified_type(),
            b'T' => {
                if matches!(self.peek_at(1), Some(b's' | b'u' | b'e')) {
                    return self.parse_elaborated_type();
                }
                let param = self.parse_template_param()?;
                if self.peek() == Some(b'I') {
                    self.d.subs.push(param);
                    let (args_start, args_end) = self.parse_template_args(false)?;
                    let sym = self.d.attach_template_args(param, args_start, args_end);
                    self.d.subs.push(sym);
                    Some(sym)
                } else {
                    self.d.subs.push(param);
                    Some(param)
                }
            }
            b'S' if self.peek_at(1) != Some(b't') => {
                let mut is_subst = false;
                let name = if self.peek() == Some(b'S') {
                    let subst = self.parse_substitution()?;
                    is_subst = true;
                    subst
                } else {
                    self.parse_unscoped_name()?
                };
                if self.peek() == Some(b'I') {
                    if !is_subst {
                        self.d.subs.push(name);
                    }
                    let (args_start, args_end) = self.parse_template_args(false)?;
                    let sym = self.d.attach_template_args(name, args_start, args_end);
                    self.d.subs.push(sym);
                    Some(sym)
                } else if is_subst {
                    Some(name)
                } else {
                    self.d.subs.push(name);
                    Some(name)
                }
            }
            _ => {
                let name = self.parse_name()?;
                self.d.subs.push(name);
                Some(name)
            }
        }
    }

    fn parse_d_type(&mut self) -> Option<Sym> {
        let builtin = match self.peek_at(1)? {
            b's' => "char16_t",
            b'i' => "char32_t",
            b'u' => "char8_t",
            b'n' => "std::nullptr_t",
            b'a' => "auto",
            b'c' => "decltype(auto)",
            b'h' => "half",
            b'd' => "decimal64",
            b'e' => "decimal128",
            b'f' => "decimal32",
            _ => return None,
        };
        self.pos += 2;
        Some(self.d.push_str(builtin))
    }

    fn parse_qualified_type(&mut self) -> Option<Sym> {
        if self.eat(b'U').is_some() {
            return None;
        }
        let mut const_qual = false;
        let mut volatile_qual = false;
        let mut restrict_qual = false;
        if self.eat(b'r').is_some() {
            restrict_qual = true;
        }
        if self.eat(b'V').is_some() {
            volatile_qual = true;
        }
        if self.eat(b'K').is_some() {
            const_qual = true;
        }
        if !const_qual && !volatile_qual && !restrict_qual {
            return None;
        }
        if self.peek() == Some(b'F') {
            let sym = self.parse_function_type(const_qual, volatile_qual, restrict_qual)?;
            self.d.subs.push(sym);
            return Some(sym);
        }
        let inner = self.parse_type()?;
        // One cv-qualifier production prints all of its flags at one slot.
        let text = match (const_qual, volatile_qual, restrict_qual) {
            (true, false, false) => " const",
            (false, true, false) => " volatile",
            (false, false, true) => " restrict",
            (true, true, false) => " const volatile",
            (true, false, true) => " const restrict",
            (false, true, true) => " volatile restrict",
            (true, true, true) => " const volatile restrict",
            (false, false, false) => return None,
        };
        let sym = self.d.wrap_cv(inner, text)?;
        self.d.subs.push(sym);
        Some(sym)
    }

    fn parse_elaborated_type(&mut self) -> Option<Sym> {
        let kind = if self.starts_with(b"Ts") {
            self.pos += 2;
            "struct "
        } else if self.starts_with(b"Tu") {
            self.pos += 2;
            "union "
        } else if self.starts_with(b"Te") {
            self.pos += 2;
            "enum "
        } else {
            return None;
        };
        let sym = self.prefixed(kind, true)?;
        self.d.subs.push(sym);
        Some(sym)
    }

    fn parse_thunk(&mut self, covariant: bool) -> Option<Sym> {
        self.enter()?;
        let parsed = self.parse_thunk_inner(covariant);
        self.leave();
        parsed
    }

    fn parse_thunk_inner(&mut self, covariant: bool) -> Option<Sym> {
        let start = self.d.buf.len() as u32;
        self.d.append(b"{virtual override thunk(");
        self.parse_call_offset()?;
        self.d.append(b", ");
        if covariant {
            self.parse_call_offset()?;
            self.d.append(b", ");
        }
        let at = self.d.buf.len() as u32;
        let enc = self.parse_encoding()?;
        self.d.place_at_cursor(enc, at)?;
        self.d.append(b")}");
        Some(Sym::span(start, self.d.buf.len() as u32))
    }

    fn parse_call_offset(&mut self) -> Option<Sym> {
        if self.eat(b'h').is_some() {
            let value = self.parse_signed_number()?;
            self.eat(b'_')?;
            return Some(self.d.push_str(&format!("{{offset({value})}}")));
        }
        if self.eat(b'v').is_some() {
            let first = self.parse_signed_number()?;
            self.eat(b'_')?;
            let second = self.parse_signed_number()?;
            self.eat(b'_')?;
            return Some(
                self.d
                    .push_str(&format!("{{virtual offset({first}, {second})}}")),
            );
        }
        None
    }

    fn parse_signed_number(&mut self) -> Option<i64> {
        let negative = self.eat(b'n').is_some();
        let value = self.parse_number()? as i64;
        Some(if negative { -value } else { value })
    }

    fn looks_like_operator(&self) -> bool {
        if self.starts_with(b"cv") || self.starts_with(b"li") {
            return true;
        }
        match (self.peek(), self.peek_at(1)) {
            (Some(a), Some(b)) => operator_symbol(a, b).is_some(),
            _ => false,
        }
    }

    fn parse_operator_name(&mut self) -> Option<Sym> {
        if self.starts_with(b"cv") {
            self.pos += 2;
            let start = self.d.buf.len() as u32;
            self.d.append(b"operator ");
            let ty = self.parse_type()?;
            if !(ty.start == start + 9 && ty.end as usize == self.d.buf.len()) {
                self.d.append_range(ty);
            }
            let mut sym = Sym::span(start, self.d.buf.len() as u32);
            sym.is_ctor = true;
            return Some(sym);
        }
        if self.starts_with(b"li") {
            self.pos += 2;
            let start = self.d.buf.len() as u32;
            self.d.append(b"operator\"\" ");
            self.parse_source_name()?;
            return Some(Sym::span(start, self.d.buf.len() as u32));
        }
        let symbol = operator_symbol(self.peek()?, self.peek_at(1)?)?;
        self.pos += 2;
        let mut text = String::from("operator");
        text.push_str(symbol);
        Some(self.d.push_str(&text))
    }

    fn parse_array_type(&mut self) -> Option<Sym> {
        self.eat(b'A')?;
        let dim = if self.eat(b'_').is_some() {
            None
        } else if matches!(self.peek(), Some(b'0'..=b'9')) {
            let number = self.parse_number()?;
            self.eat(b'_')?;
            Some(number)
        } else {
            return None;
        };
        let element = self.parse_type()?;
        self.d.wrap_array(element, dim)
    }

    fn parse_function_type(
        &mut self,
        const_qual: bool,
        volatile_qual: bool,
        restrict_qual: bool,
    ) -> Option<Sym> {
        self.eat(b'F')?;
        if self.peek() == Some(b'Y') {
            return None;
        }
        let ret = self.parse_type()?;
        if ret.suffix != NO_DECL {
            return None;
        }
        let ret = self.d.editable(ret);
        if ret.end as usize != self.d.buf.len() {
            return None;
        }
        self.d.append(b" (");
        let suffix = self.d.buf.len() as u32 - 1;
        if self.peek() == Some(b'v') && self.peek_at(1) == Some(b'E') {
            self.pos += 1;
        } else {
            let mut first = true;
            while self.peek() != Some(b'E') {
                if matches!(self.peek(), Some(b'R' | b'O')) && self.peek_at(1) == Some(b'E') {
                    break;
                }
                if !first {
                    self.d.append(b", ");
                }
                first = false;
                let cursor = self.d.buf.len() as u32;
                let param = self.parse_type()?;
                self.d.place_at_cursor(param, cursor)?;
            }
        }
        let ref_qual = if self.peek() == Some(b'R') && self.peek_at(1) == Some(b'E') {
            self.pos += 1;
            1
        } else if self.peek() == Some(b'O') && self.peek_at(1) == Some(b'E') {
            self.pos += 1;
            2
        } else {
            0
        };
        self.eat(b'E')?;
        self.d.append(b")");
        if const_qual {
            self.d.append(b" const");
        }
        if volatile_qual {
            self.d.append(b" volatile");
        }
        if restrict_qual {
            self.d.append(b" restrict");
        }
        match ref_qual {
            1 => self.d.append(b" &"),
            2 => self.d.append(b" &&"),
            _ => {}
        }
        let mut sym = Sym::span(ret.start, self.d.buf.len() as u32);
        sym.suffix = suffix;
        Some(sym)
    }

    fn parse_expression_template_arg(&mut self) -> Option<Sym> {
        self.eat(b'X')?;
        let expr = self.parse_expression()?;
        self.eat(b'E')?;
        Some(expr)
    }

    fn parse_expression(&mut self) -> Option<Sym> {
        self.parse_expr().map(|expr| expr.sym)
    }

    fn parse_expr(&mut self) -> Option<Expr> {
        self.enter()?;
        let parsed = self.parse_expr_parts();
        self.leave();
        parsed
    }

    fn parse_expr_parts(&mut self) -> Option<Expr> {
        if self.starts_with(b"pp_") {
            self.pos += 3;
            let expr = self.parse_expr()?;
            return self.prefix_text(b"++", expr);
        }
        if self.starts_with(b"mm_") {
            self.pos += 3;
            let expr = self.parse_expr()?;
            return self.prefix_text(b"--", expr);
        }
        if let (Some(first), Some(second)) = (self.peek(), self.peek_at(1)) {
            if expression_special(first, second) {
                return None;
            }
            if let Some(symbol) = operator_symbol(first, second) {
                self.pos += 2;
                return self.parse_operator_expr(symbol, operator_arity(first, second)?);
            }
        }
        if self.peek() == Some(b'T') && !matches!(self.peek_at(1), Some(b's' | b'u' | b'e' | b'L'))
        {
            let sym = self.parse_template_param()?;
            return Some(Expr { sym, paren: true });
        }
        if self.peek() == Some(b'L') {
            let external = self.starts_with(b"L_Z");
            let sym = self.parse_expr_primary()?;
            return Some(Expr {
                sym,
                paren: !external,
            });
        }
        None
    }

    fn parse_operator_expr(&mut self, symbol: &str, arity: u8) -> Option<Expr> {
        if arity == 1 && symbol == "&" && self.starts_with(b"L_Z") {
            let sym = self.parse_expr_primary()?;
            let sym = self.prefix_in_place(sym, b"&")?;
            return Some(Expr { sym, paren: true });
        }
        if arity == 1 && (symbol == "++" || symbol == "--") {
            let expr = self.parse_expr()?;
            let operand = self.subexpr(expr);
            let sym = self
                .d
                .glue(&[Glue::Sym(operand), Glue::Text(symbol.as_bytes())])?;
            return Some(Expr { sym, paren: true });
        }
        if arity == 2 && symbol == ">" {
            let lhs = self.parse_expr()?;
            let rhs = self.parse_expr()?;
            let sym = self.d.glue(&[
                Glue::Text(b"(("),
                Glue::Sym(lhs.sym),
                Glue::Text(b")>("),
                Glue::Sym(rhs.sym),
                Glue::Text(b"))"),
            ])?;
            return Some(Expr { sym, paren: true });
        }
        if arity == 3 && symbol == "?:" {
            let condition = self.parse_expr()?;
            let consequent = self.parse_expr()?;
            let alternative = self.parse_expr()?;
            let condition = self.subexpr(condition);
            let consequent = self.subexpr(consequent);
            let alternative = self.subexpr(alternative);
            let sym = self.d.glue(&[
                Glue::Sym(condition),
                Glue::Text(b"?"),
                Glue::Sym(consequent),
                Glue::Text(b" : "),
                Glue::Sym(alternative),
            ])?;
            return Some(Expr { sym, paren: true });
        }
        if arity == 1 {
            let expr = self.parse_expr()?;
            let operand = self.subexpr(expr);
            let sym = self
                .d
                .glue(&[Glue::Text(symbol.as_bytes()), Glue::Sym(operand)])?;
            return Some(Expr { sym, paren: true });
        }
        if arity == 2 {
            let lhs = self.parse_expr()?;
            let rhs = self.parse_expr()?;
            let lhs = self.subexpr(lhs);
            let rhs = self.subexpr(rhs);
            let sym = self.d.glue(&[
                Glue::Sym(lhs),
                Glue::Text(symbol.as_bytes()),
                Glue::Sym(rhs),
            ])?;
            return Some(Expr { sym, paren: true });
        }
        None
    }

    fn prefix_text(&mut self, prefix: &[u8], expr: Expr) -> Option<Expr> {
        let sym = self.d.glue(&[Glue::Text(prefix), Glue::Sym(expr.sym)])?;
        Some(Expr { sym, paren: true })
    }

    fn prefix_in_place(&mut self, sym: Sym, prefix: &[u8]) -> Option<Sym> {
        self.d.insert_at(sym.start, prefix);
        let mut sym = shift_local(sym, sym.start, prefix.len() as u32);
        // `insert_at` pushed the name past the prefix. Keep the prefix in the span.
        sym.start -= prefix.len() as u32;
        Some(sym)
    }

    fn subexpr(&mut self, expr: Expr) -> Sym {
        if !expr.paren {
            return expr.sym;
        }
        let sym = self.d.editable(expr.sym);
        self.d.insert_at(sym.start, b"(");
        self.d.append(b")");
        let mut sym = shift_local(sym, sym.start, 1);
        sym.start -= 1;
        sym.set_end(self.d.buf.len() as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::Demangler;
    use super::demangle_owned;

    fn expect(mangled: &str, demangled: &str) {
        assert_eq!(
            demangle_owned(mangled).as_deref(),
            Some(demangled),
            "{mangled}"
        );
    }

    #[test]
    fn demangles() {
        expect("_ZN3Foo3barEv", "Foo::bar");
        expect("_Z3foov", "foo");
        expect("_Z12_GLOBAL__N_1", "(anonymous namespace)");
        expect("_ZN12_GLOBAL__N_13fooEv", "(anonymous namespace)::foo");
        expect(
            "_ZN3Foo12_GLOBAL__N_13barEv",
            "Foo::(anonymous namespace)::bar",
        );
        expect(
            "_ZN12_GLOBAL__N_112_GLOBAL__N_11xEv",
            "(anonymous namespace)::(anonymous namespace)::x",
        );
        expect("_ZTVN3Foo3BarE", "{vtable(Foo::Bar)}");
        expect("_ZN3FooIiLm4EE3barEv", "Foo<int, (unsigned long)4>::bar");
        expect(
            "_ZNSt6vectorIiE9push_backERKi",
            "std::vector<int>::push_back",
        );
        expect(
            "_ZNSt6vectorIS_IiEE4sizeEv",
            "std::vector<std::vector<int> >::size",
        );
        expect("_ZN3FooC1Ev", "Foo::Foo");
        expect("_ZN3FooD1Ev", "Foo::~Foo");
        expect("_ZNK3Foo3barEv", "Foo::bar");
        expect("_ZN3FooUt_3barEv", "Foo::{unnamed type#1}::bar");
        expect("_ZZN3Foo3barEvE3baz", "Foo::bar()::baz");
        expect("_ZZN3FooC1EDnE3bar", "Foo::Foo(std::nullptr_t)::bar");
        expect("_ZN3FooUlvE_3barEv", "Foo::{lambda()#1}::bar");
        expect("_ZN3FooUlvE_clEv", "Foo::{lambda()#1}::operator()");
        expect("_ZN3FooUlT_E_clEi", "Foo::{lambda(auto)#1}::operator()");
        expect(
            "_ZN3FooUlT_T0_E_clEii",
            "Foo::{lambda(auto, auto)#1}::operator()",
        );
        expect("_ZN3FooUlPT_E_clEPi", "Foo::{lambda(auto*)#1}::operator()");
        expect(
            "_ZN3FooUlRKT_E_clERKi",
            "Foo::{lambda(auto const&)#1}::operator()",
        );
        expect(
            "_ZN3FooUlSt6vectorIT_EE_clEv",
            "Foo::{lambda(std::vector<auto>)#1}::operator()",
        );
        expect("_ZN3Foo3barIiEUlT_E_Ev", "Foo::bar<int>::{lambda(auto)#1}");
        expect(
            "_ZZN3Foo3barEvENUlT_E_4callEv",
            "Foo::bar()::{lambda(auto)#1}::call",
        );
        expect("_ZZN3Foo3barIiE3bazET_E1x", "Foo::bar<int>::baz(int)::x");
        expect("_ZN3FooaSERS_", "Foo::operator=");
        expect("_ZN3FoonwEm", "Foo::operator new");
        expect("_ZN3FoocviEv", "Foo::operator int");
        expect("_ZNO3Foo3barEv", "Foo::bar &&");
        expect("_ZZNK3Foo3barEvE3baz", "Foo::bar() const::baz");
        expect(
            "_ZZN3Foo3barEvENKUlvE_clEv",
            "Foo::bar()::{lambda()#1}::operator() const",
        );
        expect(
            "_ZThn8_N3Foo3barEv",
            "{virtual override thunk({offset(-8)}, Foo::bar)}",
        );
        expect(
            "_ZTcv0_n16_h8_N3Foo3barEv",
            "{virtual override thunk({virtual offset(0, -16)}, {offset(8)}, Foo::bar)}",
        );
        expect("_Z1fIN3Foo3BarERKS1_Ev", "f<Foo::Bar, Foo::Bar const&>");
        expect(
            "_ZGVZN3Foo3barEvE3baz",
            "guard variable for Foo::bar()::baz",
        );
        expect(
            "_ZN3Foo3barIZN3Bar3bazIcEEvRNS_4ListIT_EEEUlvE_EEv",
            "Foo::bar<Bar::baz<char>(Foo::List<char>&)::{lambda()#1}>",
        );
        expect("_ZN3Foo5applyIJ3Bar3BazEEEv", "Foo::apply<Bar, Baz>");
        expect("_Z1fIA_cEv", "f<char []>");
        expect("_Z1fIA10_iEv", "f<int [10]>");
        expect("_Z1fIRA12_KcEv", "f<char const (&) [12]>");
        expect("_Z1fIPFbRKiS1_EEv", "f<bool (*)(int const&, int const&)>");
        expect("_Z1fIM3FooFvvEE", "f<void (Foo::*)()>");
        expect("_Z1fIM3FooKFbvEE", "f<bool (Foo::*)() const>");
        expect("_Z1fIM3FooFiEE", "f<int (Foo::*)()>");
        expect("_Z1fIM3FooFiiEE", "f<int (Foo::*)(int)>");
        expect("_Z1fIM3FooiE", "f<int Foo::*>");
        expect(
            "_ZTIMN4llvm4json6ObjectEKFSt8optionalINS_9StringRefEES3_E",
            "typeinfo for std::optional<llvm::StringRef> (llvm::json::Object::*)(llvm::StringRef) const",
        );
        expect("_Z1fIXadL_ZN3Foo3barEiEEEv", "f<&Foo::bar(int)>");
        expect("_Z1fIXgtLi1ELi2EEEv", "f<((1)>(2))>");
        expect("_ZN3FooD0B8nn180100Ev", "Foo::~Foo[abi:nn180100]");
        expect("_ZN3Foo3barB3abcEv", "Foo::bar[abi:abc]");
    }

    #[test]
    fn reuses_its_buffers() {
        let mut demangler = Demangler::new();
        let first = demangler.demangle("_ZN3Foo3barEv").unwrap().to_string();
        let second = demangler.demangle("_ZN3FooC1Ev").unwrap().to_string();
        assert_eq!(first, "Foo::bar");
        assert_eq!(second, "Foo::Foo");
        assert_eq!(
            demangler.demangle("_ZNSt6vectorIS_IiEE4sizeEv"),
            Some("std::vector<std::vector<int> >::size")
        );
    }

    #[test]
    fn rejects_what_it_does_not_implement() {
        assert_eq!(demangle_owned("malloc"), None);
        assert_eq!(demangle_owned("_RNvC3foo3bar"), None);
        assert_eq!(demangle_owned("_ZN3Foov1abcE"), None);
        assert_eq!(demangle_owned("_ZN3Foo5valueE"), None);
        assert_eq!(demangle_owned("_ZN13_$LT$test$GT$E"), None);
        assert_eq!(demangle_owned("_ZN3foo3bar17h0123456789abcdefE"), None);
        assert_eq!(demangle_owned("_ZN3foo3barE.llvm.1234"), None);
        assert_eq!(demangle_owned("__ZN3foo3barE"), None);
        assert_eq!(demangle_owned("ZN3foo3barE"), None);
    }
    #[test]
    fn limits_argument_pack_depth() {
        let mut demangler = Demangler::new();
        let depth = super::MAX_DEPTH as usize * 2;
        let name = format!("_Z1fI{}i{}Evv", "J".repeat(depth), "E".repeat(depth));
        assert!(demangler.demangle(&name).is_none());
        assert_eq!(demangler.demangle("_Z1fIJiEEvv"), Some("f<int>"));
    }

    #[test]
    fn limits_thunk_depth() {
        let mut demangler = Demangler::new();
        let name = format!("_Z{}1fv", "Th0_".repeat(super::MAX_DEPTH as usize * 2));
        assert!(demangler.demangle(&name).is_none());
        assert_eq!(
            demangler.demangle("_ZTh0_1fv"),
            Some("{virtual override thunk({offset(0)}, f)}")
        );
    }
    #[test]
    fn rejects_out_of_bounds_source_name_lengths() {
        let mut demangler = Demangler::new();
        for name in [
            format!("_Z{}", usize::MAX),
            format!("_Z{}x", usize::MAX - 1),
            "_Z4foo".to_owned(),
            "_Z0".to_owned(),
        ] {
            assert_eq!(demangler.demangle(&name), None, "{name}");
        }
        assert_eq!(demangler.demangle("_Z3foo"), Some("foo"));
    }
    #[test]
    fn preserves_pointer_declarator_order() {
        expect("_Z1fIJRPFvvEEEvv", "f<void (*&)()>");
        expect("_Z1fIJRKPFvvEEEvv", "f<void (* const&)()>");
        expect("_Z1fIJOPFvvEEEvv", "f<void (*&&)()>");
        expect("_Z1fIJPPFvvEEEvv", "f<void (**)()>");
        expect("_Z1fIJRPA3_iEEvv", "f<int (*&) [3]>");
    }
    #[test]
    fn preserves_expression_parentheses() {
        expect("_Z1fIXplLi1ELi2EEEvv", "f<(1)+(2)>");
        expect("_Z1fIXngLi1EEEvv", "f<-(1)>");
        expect("_Z1fIXmlplLi1ELi2ELi3EEEvv", "f<((1)+(2))*(3)>");
        expect(
            "_ZZ4exprILi2EEv1AIXplT_Li1EEEE3var",
            "expr<2>(A<(2)+(1)>)::var",
        );
    }
    #[test]
    fn qualifies_complete_nested_types() {
        expect(
            "_Z1fIJN3Foo3BarENS1_3BazERKS2_EEvv",
            "f<Foo::Bar, Foo::Bar::Baz, Foo::Bar::Baz const&>",
        );
        expect(
            "_Z1fIN3Foo3BarENS1_3BazERKS2_Ev",
            "f<Foo::Bar, Foo::Bar::Baz, Foo::Bar::Baz const&>",
        );
        expect(
            "_Z1fIN3Foo3BarENS1_3BazERS2_Ev",
            "f<Foo::Bar, Foo::Bar::Baz, Foo::Bar::Baz&>",
        );
        expect(
            "_Z1fIN3Foo3BarENS1_3BazEPS2_Ev",
            "f<Foo::Bar, Foo::Bar::Baz, Foo::Bar::Baz*>",
        );
        expect(
            "_Z1fIN3Foo3BarENS1_3BazERVKS2_Ev",
            "f<Foo::Bar, Foo::Bar::Baz, Foo::Bar::Baz const volatile&>",
        );
        expect(
            "_Z1fIN3Foo3BarENS1_IiE3BazERKS3_Ev",
            "f<Foo::Bar, Foo::Bar<int>::Baz, Foo::Bar<int>::Baz const&>",
        );
    }
    #[test]
    fn keeps_qualifiers_on_member_function_types() {
        expect("_Z1fIJM1DKFvN1N1TEEEEvv", "f<void (D::*)(N::T) const>");
        expect("_Z1fIJM1DVFvN1N1TEEEEvv", "f<void (D::*)(N::T) volatile>");
        expect(
            "_Z1fIJM1DVKFvN1N1TEEEEvv",
            "f<void (D::*)(N::T) const volatile>",
        );
        expect("_Z1fIJM1DFvN1N1TEREEEvv", "f<void (D::*)(N::T) &>");
        expect("_Z1fIJM1DKFvN1N1TEOEEEvv", "f<void (D::*)(N::T) const &&>");
        expect(
            "_Z1fIJM1DKFvKN1N1TEEEEvv",
            "f<void (D::*)(N::T const) const>",
        );
    }
    #[test]
    fn preserves_literal_operator_names() {
        expect("_Zli4_fooe", "operator\"\" _foo");
        expect("_ZN1Nli4_fooEe", "N::operator\"\" _foo");
        expect(
            "_Zli4_numIJLc49ELc50EEEiv",
            "operator\"\" _num<(char)49, (char)50>",
        );
    }
}
