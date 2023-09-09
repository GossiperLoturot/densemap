use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn insertion(c: &mut Criterion) {
    let mut g = c.benchmark_group("insertion");
    g.bench_function("densemap", |b| {
        let mut densemap = densemap::DenseMap::new();
        b.iter(|| {
            for _ in 0..10000 {
                let key = densemap.insert(black_box(0));
                black_box(key);
            }
        });
    });
    g.bench_function("slotmap", |b| {
        let mut slotmap = slotmap::SlotMap::new();
        b.iter(|| {
            for _ in 0..10000 {
                let key = slotmap.insert(black_box(0));
                black_box(key);
            }
        });
    });
    g.bench_function("hop slotmap", |b| {
        let mut slotmap = slotmap::HopSlotMap::new();
        b.iter(|| {
            for _ in 0..10000 {
                let key = slotmap.insert(black_box(0));
                black_box(key);
            }
        });
    });
    g.bench_function("dense slotmap", |b| {
        let mut slotmap = slotmap::DenseSlotMap::new();
        b.iter(|| {
            for _ in 0..10000 {
                let key = slotmap.insert(black_box(0));
                black_box(key);
            }
        });
    });
}

fn remove(c: &mut Criterion) {
    let mut g = c.benchmark_group("remove");
    g.bench_function("densemap", |b| {
        let mut densemap = densemap::DenseMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = densemap.insert(0);
            keys.push(key);
        }
        b.iter(|| {
            let mut densemap = densemap.clone();
            for key in keys.iter() {
                let value = densemap.remove(*key);
                black_box(value);
            }
        });
    });
    g.bench_function("slotmap", |b| {
        let mut slotmap = slotmap::SlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        b.iter(|| {
            let mut slotmap = slotmap.clone();
            for key in keys.iter() {
                let value = slotmap.remove(*key);
                black_box(value);
            }
        });
    });
    g.bench_function("hop slotmap", |b| {
        let mut slotmap = slotmap::HopSlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        b.iter(|| {
            let mut slotmap = slotmap.clone();
            for key in keys.iter() {
                let value = slotmap.remove(*key);
                black_box(value);
            }
        });
    });
    g.bench_function("dense slotmap", |b| {
        let mut slotmap = slotmap::DenseSlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        b.iter(|| {
            let mut slotmap = slotmap.clone();
            for key in keys.iter() {
                let value = slotmap.remove(*key);
                black_box(value);
            }
        });
    });
}

fn reinsertion(c: &mut Criterion) {
    let mut g = c.benchmark_group("reinsertion");
    g.bench_function("densemap", |b| {
        let mut densemap = densemap::DenseMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = densemap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            densemap.remove(*key);
        }
        b.iter(|| {
            let mut densemap = densemap.clone();
            for _ in 0..10000 {
                let key = densemap.insert(black_box(0));
                black_box(key);
            }
        });
    });
    g.bench_function("slotmap", |b| {
        let mut slotmap = slotmap::SlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            slotmap.remove(*key);
        }
        b.iter(|| {
            let mut slotmap = slotmap.clone();
            for _ in 0..10000 {
                let key = slotmap.insert(black_box(0));
                black_box(key);
            }
        });
    });
    g.bench_function("hop slotmap", |b| {
        let mut slotmap = slotmap::HopSlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            slotmap.remove(*key);
        }
        b.iter(|| {
            let mut slotmap = slotmap.clone();
            for _ in 0..10000 {
                let key = slotmap.insert(black_box(0));
                black_box(key);
            }
        });
    });
    g.bench_function("dense slotmap", |b| {
        let mut slotmap = slotmap::DenseSlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            slotmap.remove(*key);
        }
        b.iter(|| {
            let mut slotmap = slotmap.clone();
            for _ in 0..10000 {
                let key = slotmap.insert(black_box(0));
                black_box(key);
            }
        });
    });
}

fn iteration(c: &mut Criterion) {
    let mut g = c.benchmark_group("iteration");
    g.bench_function("densemap", |b| {
        let mut densemap = densemap::DenseMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = densemap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            densemap.remove(*key);
        }
        for _ in 0..10000 {
            densemap.insert(0);
        }
        b.iter(|| {
            for value in densemap.iter() {
                black_box(value);
            }
        });
    });
    g.bench_function("slotmap", |b| {
        let mut slotmap = slotmap::SlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            slotmap.remove(*key);
        }
        for _ in 0..10000 {
            slotmap.insert(black_box(0));
        }
        b.iter(|| {
            for value in slotmap.iter() {
                black_box(value);
            }
        });
    });
    g.bench_function("hop slotmap", |b| {
        let mut slotmap = slotmap::HopSlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            slotmap.remove(*key);
        }
        for _ in 0..10000 {
            slotmap.insert(black_box(0));
        }
        b.iter(|| {
            for value in slotmap.iter() {
                black_box(value);
            }
        });
    });
    g.bench_function("dense slotmap", |b| {
        let mut slotmap = slotmap::DenseSlotMap::new();
        let mut keys = vec![];
        for _ in 0..10000 {
            let key = slotmap.insert(0);
            keys.push(key);
        }
        for key in keys.iter() {
            slotmap.remove(*key);
        }
        for _ in 0..10000 {
            slotmap.insert(black_box(0));
        }
        b.iter(|| {
            for value in slotmap.iter() {
                black_box(value);
            }
        });
    });
}

criterion_group!(benches, insertion, remove, reinsertion, iteration);
criterion_main!(benches);
