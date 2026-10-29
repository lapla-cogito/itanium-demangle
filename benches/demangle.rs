use std::hint::black_box;

use cpp_demangle::{DemangleOptions, Symbol};
use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use itanium_demangle::Demangler;

const SYMBOLS: &str = include_str!("../test-data/llvm-1k.txt");

fn demangle(c: &mut Criterion) {
    let symbols: Vec<_> = SYMBOLS.lines().collect();
    let mut group = c.benchmark_group("demangle");
    group.throughput(Throughput::Bytes(SYMBOLS.len() as u64));

    let mut demangler = Demangler::new();
    group.bench_function("itanium_demangle", |b| {
        b.iter(|| {
            for &symbol in &symbols {
                black_box(demangler.demangle(black_box(symbol)));
            }
        });
    });

    let options = DemangleOptions::new().no_params().no_return_type();
    group.bench_function("cpp_demangle", |b| {
        b.iter(|| {
            for &symbol in &symbols {
                let parsed = Symbol::new(black_box(symbol.as_bytes())).unwrap();
                black_box(parsed.demangle_with_options(&options).unwrap());
            }
        });
    });

    group.finish();
}

criterion_group!(benches, demangle);
criterion_main!(benches);
