//! Interactive Shuffle Benchmark Tool
//! 
//! Usage:
//! cargo run --bin shuffle_bench --release -- --n 4096 --k 4 --d 6 --samples 10
//! cargo run --bin shuffle_bench --release -- --interactive

extern crate clap;
use clap::{App, Arg};
use std::io::{self, Write};

fn main() {
    let matches = App::new("Shuffle Proof Benchmark")
        .version("1.0")
        .about("Interactive benchmark tool for shuffle proofs")
        .arg(Arg::with_name("n")
            .short("n")
            .long("n")
            .value_name("SIZE")
            .help("Number of ciphertexts")
            .takes_value(true))
        .arg(Arg::with_name("k")
            .short("k")
            .long("k")
            .value_name("K")
            .help("Folding factor")
            .takes_value(true))
        .arg(Arg::with_name("d")
            .short("d")
            .long("d")
            .value_name("D")
            .help("Recursion depth")
            .takes_value(true))
        .arg(Arg::with_name("samples")
            .short("s")
            .long("samples")
            .value_name("N")
            .help("Number of samples (default: 10)")
            .takes_value(true))
        .arg(Arg::with_name("interactive")
            .short("i")
            .long("interactive")
            .help("Interactive mode"))
        .get_matches();

    if matches.is_present("interactive") {
        run_interactive();
    } else {
        run_cli(&matches);
    }
}

fn run_interactive() {
    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║          Interactive Shuffle Proof Benchmark                 ║");
    println!("╚══════════════════════════════════════════════════════════════╝\n");

    let n = prompt_usize("Enter n (number of ciphertexts)", 4096);
    let k = prompt_usize("Enter k (folding factor, 2-16)", 4);
    let d = prompt_usize("Enter d (recursion depth)", calc_d(n, k));
    let samples = prompt_usize("Enter number of samples", 10);

    println!("\n{}", "=".repeat(64));
    println!("Configuration:");
    println!("  n = {} ciphertexts", n);
    println!("  k = {} (folding factor)", k);
    println!("  d = {} (recursion depth)", d);
    println!("  samples = {}", samples);
    println!("{}", "=".repeat(64));

    let est_time = estimate_time(n, samples);
    println!("\nEstimated runtime: {:.1} minutes", est_time);

    if prompt_bool("\nProceed?", true) {
        run_benchmark(n, k, d, samples);
    } else {
        println!("Cancelled.");
    }
}

fn run_cli(matches: &clap::ArgMatches) {
    let n = matches.value_of("n")
        .and_then(|s| s.parse().ok())
        .unwrap_or(4096);
    
    let k = matches.value_of("k")
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);
    
    let d = matches.value_of("d")
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| calc_d(n, k));
    
    let samples = matches.value_of("samples")
        .and_then(|s| s.parse().ok())
        .unwrap_or(10);

    println!("\n╔══════════════════════════════════════════════════════════════╗");
    println!("║                  Shuffle Benchmark                            ║");
    println!("╚══════════════════════════════════════════════════════════════╝");
    println!("\nConfiguration: n={}, k={}, d={}, samples={}", n, k, d, samples);
    println!("Estimated time: {:.1} minutes\n", estimate_time(n, samples));
    
    run_benchmark(n, k, d, samples);
}

fn run_benchmark(n: usize, k: usize, d: usize, samples: usize) {
    println!("\nTo run this benchmark, use:");
    println!("  cargo bench --bench r1cs --features yoloproofs -- \\");
    println!("    \"n={}\" --sample-size {}", n, samples);
    println!("\nOr for interactive exploration, you can:");
    println!("  1. Edit benches/r1cs.rs");
    println!("  2. Change n_input to {}", n);
    println!("  3. Run: cargo bench\n");
}

fn prompt_usize(message: &str, default: usize) -> usize {
    print!("{} [{}]: ", message, default);
    io::stdout().flush().unwrap();
    
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    
    input.trim().parse().unwrap_or(default)
}

fn prompt_bool(message: &str, default: bool) -> bool {
    let default_str = if default { "Y/n" } else { "y/N" };
    print!("{} [{}]: ", message, default_str);
    io::stdout().flush().unwrap();
    
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    
    match input.trim().to_lowercase().as_str() {
        "y" | "yes" => true,
        "n" | "no" => false,
        "" => default,
        _ => default,
    }
}

fn calc_d(n: usize, k: usize) -> usize {
    ((n as f64).log(k as f64).ceil() as usize).max(1)
}

fn estimate_time(n: usize, samples: usize) -> f64 {
    // Rough estimate: scale from n=1M baseline
    let base_time = 311.0; // seconds for n=1M from paper
    let estimated = (n as f64 / 1048576.0) * base_time * samples as f64;
    estimated / 60.0 // convert to minutes
}
