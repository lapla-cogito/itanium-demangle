#![feature(test)]

extern crate test;

use std::hint::black_box;

use cpp_demangle::{DemangleOptions, Symbol};
use itanium_demangle::Demangler;
use test::Bencher;

const SYMBOLS: &str = include_str!("../test-data/llvm-1k.txt");

#[bench]
fn itanium_demangle(b: &mut Bencher) {
    let symbols: Vec<_> = SYMBOLS.lines().collect();
    let mut demangler = Demangler::new();

    b.iter(|| {
        for &symbol in &symbols {
            black_box(demangler.demangle(black_box(symbol)));
        }
    });
    b.bytes = SYMBOLS.len() as u64;
}

#[bench]
fn cpp_demangle(b: &mut Bencher) {
    let symbols: Vec<_> = SYMBOLS.lines().collect();
    let options = DemangleOptions::new().no_params().no_return_type();

    b.iter(|| {
        for &symbol in &symbols {
            let parsed = Symbol::new(black_box(symbol.as_bytes())).unwrap();
            black_box(parsed.demangle_with_options(&options).unwrap());
        }
    });
    b.bytes = SYMBOLS.len() as u64;
}
