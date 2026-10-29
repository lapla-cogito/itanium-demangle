# itanium-demangle

A fast [Itanium C++ ABI] demangler.

```rust
use itanium_demangle::Demangler;

let mut demangler = Demangler::new();
assert_eq!(demangler.demangle("_ZN3Foo3barEv"), Some("Foo::bar"));
```

## Motivation

Rust has fast demanglers for the other common ABIs, including [rustc-demangle] and [msvc-demangler]. For Itanium names, the usual Rust library is [cpp_demangle]. It parses each name into an owned syntax tree and substitution table, then walks that tree into a new string. That is slow when a program demangles many names.

In this crate, `Demangler` writes the display text into one buffer and records substitutions as ranges in that buffer. The buffer and the table stay allocated for the next name.

## Performance

Measured on a ThinkPad T14s Gen 7.

The input is the 49,163 unique exported Itanium names (`_Z` / `__Z`) in Ubuntu's `/usr/lib/x86_64-linux-gnu/libLLVM.so.21.1` (LLVM 21.1.8).

One `Demangler` is reused for every name. `cpp_demangle` 0.5.1 is called with `no_params` and `no_return_type`. Each run demangles the whole list once.

| | Median (whole list) | Per name |
| --- | ---: | ---: |
| `itanium-demangle` | 9.2 ms | 187 ns |
| `cpp_demangle` 0.5.1 | 77.2 ms | 1.57 µs |

Once can run the Criterion benchmark locally for random subset of the libLLVM symbols:

```sh
cargo bench
```

[Itanium C++ ABI]: https://itanium-cxx-abi.github.io/cxx-abi/abi.html#mangling
[cpp_demangle]: https://crates.io/crates/cpp_demangle
[rustc-demangle]: https://crates.io/crates/rustc-demangle
[msvc-demangler]: https://crates.io/crates/msvc-demangler
