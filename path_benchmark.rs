use criterion::{criterion_group, criterion_main, Criterion, BatchSize};
use lib::{path_graph, rand_graph, wl_one_graph};
use rand_chacha::rand_core::SeedableRng;
use rand::Rng;
use rand_chacha;

fn path_benchmark(c: &mut Criterion) {
    // Numbers of vertices we'll be testing
    let possible_sizes = [500, 1000, 2000];

    let mut group = c.benchmark_group("paths");

    for size in possible_sizes {
        // No problems with shadowing/aliasing/etc. here??

        // Name the trial
        let id = format!("{size} vertices");
        // Setup code (not timed) -- create the path
        let adjacencies: Vec<Vec<usize>> = path_graph(size);

        group.bench_function(id, |b| 
            b.iter( || wl_one_graph(&adjacencies))
        );
    }

    group.finish();
}

fn rand_benchmark(c: &mut Criterion) {
    // Numbers of vertices we'll be testing
    let possible_sizes = [500, 1000, 2000];
    // Density of random graphs
    let p = 0.5;

    let mut group = c.benchmark_group("random graphs");

    for size in possible_sizes {
        // Name the trial
        let id = format!("{size} vertices");

        group.bench_function(id, |b| 
            {
                // Seed global rng, so same set of random graphs will be used every time
                // Does it make sense to do this at each size, as opposed to just once
                // at the beginning?
                let mut rng = rand_chacha::ChaCha8Rng::seed_from_u64(0);
        
                b.iter_batched_ref(
                    // Set up different random graph (I think?) for each trial -- not timed
                    || -> Vec<Vec<usize>> { rand_graph(size, p, rng.gen::<u64>()) },
                    |adj| wl_one_graph(adj),
                    BatchSize::SmallInput,
                )
        
            }
        );
    }

    group.finish();
}


criterion_group!(benches, rand_benchmark, path_benchmark);
criterion_main!(benches);