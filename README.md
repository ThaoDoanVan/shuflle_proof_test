# Shuffle Proof Implementation

This repository contains the implementation of the shuffle proof system described in our paper. The code is written in Rust and provides benchmarks to reproduce the experimental results presented in the paper.


## Table of Contents
- [Installation](#native-installation)
  - [Prerequisites](#prerequisites)
  - [Installation](#installation)
  - [Building the Project](#building-the-project)
- [Running Benchmarks](#running-benchmarks)
- [Project Structure](#project-structure)
- [Reproducing Paper Results](#reproducing-paper-results)
- [Troubleshooting](#troubleshooting)
- [Contact](#contact)

## Prerequisites

This project requires **Rust 1.81 or newer**. We strongly recommend using `rustup`, the official Rust toolchain installer.

### System Requirements
- Linux, macOS, or Windows with WSL
- At least 4GB RAM
- ~500MB disk space for Rust toolchain and dependencies

## Installation

### Step 1: Install Rust (if not already installed)

If you don't have Rust installed or have an older version:

```bash
# Install rustup (Rust installer and version manager)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Follow the on-screen instructions (usually just press 1 for default installation)

# After installation completes, load Rust into your current shell
source $HOME/.cargo/env
```

**If you already have Rust installed via system packages (apt, dnf, etc.):**

We recommend removing the system version and using rustup instead:

```bash
# For Ubuntu/Debian users
sudo apt remove rustc cargo

# Then install rustup as shown above
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

### Step 2: Verify Rust Installation

```bash
rustc --version
# Should show: rustc 1.81.0 or newer

cargo --version
# Should show: cargo 1.81.0 or newer
```

If you see an older version (like 1.75.0), update Rust:

```bash
rustup update stable
rustup default stable
```

### Step 3: Clone the Repository

```bash
git clone https://github.com/ThaoDoanVan/shuflle_proof_test.git
cd shuflle_proof_test
```

## Building the Project

Build the project in release mode (optimized for performance):

```bash
cargo build --release
```

This will:
- Download and compile all dependencies (may take 5-10 minutes on first build)
- Compile the project with optimizations
- Place the compiled binaries in `target/release/`

**Note:** The first build will take longer as Cargo downloads and compiles all dependencies. Subsequent builds will be much faster.

## Running Benchmarks

The main benchmarks can be run with:

```bash
# Run the R1CS benchmark with yoloproofs feature
cargo bench --bench r1cs --features yoloproofs
```

This will execute the performance benchmarks and output timing results. The benchmark may take several minutes to complete depending on your hardware.

If any tests fail, please see the [Troubleshooting](#troubleshooting) section.

### Available Benchmarks

- `r1cs` - Benchmarks for the R1CS shuffle proof system

To see all available benchmarks:

```bash
ls benches/
```

To run a specific benchmark:

```bash
cargo bench --bench <benchmark_name> --features yoloproofs
```

## Project Structure

```
shuflle_proof_test/
├── benches/          # Benchmark code
│   └── r1cs.rs       # R1CS shuffle proof benchmarks
├── docs/             # Documentation
├── examples/         # Example usage (if any)
├── src/              # Main source code
│   └── lib.rs        # Library entry point
├── tests/            # Integration tests
├── target/           # Build artifacts (generated, not in git)
├── Cargo.toml        # Project configuration and dependencies
├── Cargo.lock        # Locked dependency versions (for reproducibility)
├── README.md         # This file
└── LICENSE.txt       # MIT License
```

## Reproducing Paper Results

To reproduce the experimental results from our paper:

### Benchmark X (Table/Figure Y)

```bash
cargo bench --bench r1cs --features yoloproofs
```

**Expected output:**

**Hardware used in paper:**
- CPU: Intel Core i5-1245U CPU (up to 4.4 GHz)
- RAM: 16GB
- OS: 22.04 LTS

**Note:** Actual performance may vary depending on your hardware. The relative performance characteristics should remain consistent.

## Troubleshooting

### Error: "rustc 1.81 or newer required"

**Solution:** Update your Rust installation:

```bash
rustup update stable
rustup default stable
rustc --version  # Verify version is 1.81+
```

### Error: "lock file version 4 requires `-Znext-lockfile-bump`"

**Solution:** This means your Rust version is too old. Update to Rust 1.81 or newer (see above).

### Error: "command 'rustup' not found"

**Solution:** You need to install rustup. See [Installation](#installation) section above.

### Error: Package dependencies cannot be built

**Solution:** Make sure you're using Rust 1.81 or newer:

```bash
rustc --version
# If version is < 1.81, run:
rustup update stable
```

### Benchmarks are running slowly

Benchmarks are computationally intensive and may take several minutes. Make sure you're running in release mode (`cargo bench` automatically uses release mode). If you need faster feedback, you can reduce the iteration count by modifying the benchmark files in `benches/`.

### Still having issues?

Please check that:
1. ✅ You have Rust 1.81 or newer (`rustc --version`)
2. ✅ You're in the correct directory (`cd shuflle_proof_test`)
3. ✅ You have internet connection (for downloading dependencies)
4. ✅ You have sufficient disk space (~500MB for Rust + dependencies)


## License

This project is licensed under the MIT License - see the [LICENSE.txt](LICENSE.txt) file for details.
