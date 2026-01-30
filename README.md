# Shuffle Proof Implementation

This repository contains the implementation of a logarithmic-size shuffle proof system. The code is written in Rust and provides benchmarks to reproduce the experimental results presented in the associated research paper.

## Table of Contents
- [Installation](#installation)
  - [Prerequisites](#prerequisites)
  - [Step 1: Install Rust](#step-1-install-rust-if-not-already-installed)
  - [Step 2: Verify Installation](#step-2-verify-rust-installation)
  - [Step 3: Clone Repository](#step-3-clone-the-repository)
  - [Step 4: Build Project](#step-4-building-the-project)
- [Running Benchmarks](#running-benchmarks)
  - [Quick Validation](#quick-validation)
  - [Reproducing Paper Results](#reproducing-paper-results)
  - [Custom Parameter Testing](#custom-parameter-testing)
  - [Verificatum Comparison](#verificatum-comparison)
- [Project Structure](#project-structure)
- [Troubleshooting](#troubleshooting)
- [License](#license)

## Installation

### Prerequisites

This project requires **Rust 1.81 or newer**. We recommend using `rustup`, the official Rust toolchain installer.

**System Requirements:**
- Linux, macOS, or Windows with WSL
- 4GB RAM minimum
- ~500MB disk space for Rust toolchain and dependencies

### Step 1: Install Rust (if not already installed)

If you don't have Rust installed:

```bash
# Install rustup
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Follow on-screen instructions (press 1 for default installation)

# Load Rust into current shell
source $HOME/.cargo/env
```

If you have Rust installed via system packages (apt, dnf, etc.), we recommend using rustup instead:

```bash
# For Ubuntu/Debian
sudo apt remove rustc cargo

# Then install rustup
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

If you see an older version, update Rust:

```bash
rustup update stable
rustup default stable
```

### Step 3: Clone the Repository

```bash
git clone https://github.com/ThaoDoanVan/shufffle_proof_test.git
cd shuflle_proof_test
```

### Step 4: Building the Project

Build the project in release mode:

```bash
cargo build --release
```

This will download and compile all dependencies. The first build may take 5-10 minutes. Subsequent builds will be faster.

## Running Benchmarks

### Quick Validation

Verify the implementation with a fast test:

```bash
cargo bench --bench quick --features yoloproofs
```

This runs two small-scale tests (n=1024 and n=4096) to confirm the code is working correctly.

### Reproducing Paper Results

#### Table 1: Prover Performance

Compare prover efficiency with different configurations:

```bash
cargo bench --bench table1 --features yoloproofs
```

This tests multiple input sizes (n ∈ {1024, 4096, 16384, 65536}) and folding factors (k ∈ {2, 4}).

#### Table 2: Verifier Performance

Measure verifier efficiency:

```bash
cargo bench --bench table2 --features yoloproofs
```

This demonstrates verifier performance across different input scales with k=4.

### Custom Parameter Testing

To test with your own parameters:

1. **Edit the configuration file**: Open `benches/r1cs.rs` in a text editor

2. **Modify lines 28-43**:

```rust
const N: usize = 4096;           // Number of ciphertexts
const K: usize = 4;              // Folding factor
const D: usize = 6;              // Recursion depth
const SAMPLES: usize = 5;        // Number of samples (3-10 recommended)
```

3. **Run the custom benchmark**:

```bash
cargo bench --bench r1cs --features yoloproofs
```

**Parameter Guidelines:**
- **N**: Number of ciphertexts to shuffle. Best results when N is a power of K.
- **K**: Folding factor. Higher values reduce proof size. Typically 2, 3, 4, 5.
- **D**: Recursion depth. Should satisfy N ≈ K^D for optimal performance.
- **SAMPLES**: More samples provide more accurate timing (3 = fast, 10 = accurate).

### Verificatum Comparison

This repository includes a benchmark script for comparing performance with Verificatum, an established mix-net implementation used in real-world elections.

#### Prerequisites for Verificatum Benchmarks

1. **Install Verificatum VMN**:
   - Download from: https://www.verificatum.org/
   - Follow installation instructions for your platform

2. **System Requirements**:
   - At least 12GB RAM available
   - Single-threaded CPU core for fair comparison

#### Running Verificatum Benchmarks

1. **Make script executable**:
   ```bash
   chmod +x benchmarks/verificatum_benchmark.sh
   ```

2. **Run benchmarks**:
   ```bash
   ./benchmarks/verificatum_benchmark.sh
   ```

The script will:
- Pre-warm the JVM for consistent measurements
- Test multiple input sizes (matching Rust benchmarks)
- Generate timing and proof size statistics
- Save results to a timestamped directory

#### Understanding the Output

The script produces:
- **Per-iteration logs**: `verificatum_N<size>.csv` - Detailed timing for each iteration
- **Summary report**: `summary.csv` - Aggregate statistics for all tested sizes

Results include:
- Prover time (milliseconds)
- Verifier time (milliseconds)
- Proof size (bytes)

#### Comparison with Rust Implementation

After running both benchmarks:

```bash
# Rust results (from Criterion output)
cargo bench --bench table1 --features yoloproofs

# Verificatum results
cat results_*/summary.csv
```

## Project Structure

```
shuflle_proof_test/
├── benches/
│   ├── quick.rs              # Quick validation (fast test)
│   ├── table1.rs             # Paper Table 1 (prover performance)
│   ├── table2.rs             # Paper Table 2 (verifier performance)
│   ├── r1cs.rs               # Custom parameters (user-editable)
│   └── verificatum_benchmark.sh  # Verificatum comparison script
├── src/
│   ├── lib.rs                # Library entry point
│   ├── r1cs/
│   │   ├── proof.rs          # Proof structure
│   │   ├── prover.rs         # Proving algorithm
│   │   ├── verifier.rs       # Verification algorithm
│   │   └── inner_product_proof.rs  # Inner product arguments
│   └── ...
├── Cargo.toml                # Project configuration
├── Cargo.lock                # Locked dependencies
├── LICENSE.txt               # MIT License
└── README.md                 # This file
```

## Benchmark Commands Reference

| Benchmark | Command | Purpose |
|-----------|---------|---------|
| **Quick Validation** | `cargo bench --bench quick --features yoloproofs` | Fast correctness check |
| **Table 1** | `cargo bench --bench table1 --features yoloproofs` | Prover performance (paper) |
| **Table 2** | `cargo bench --bench table2 --features yoloproofs` | Verifier performance (paper) |
| **Custom** | `cargo bench --bench r1cs --features yoloproofs` | User-defined parameters |
| **Verificatum** | `./benchmarks/verificatum_benchmark.sh` | Comparison baseline |

## Hardware Information

The benchmarks in the paper were conducted on:
- **CPU**: Intel Core i5-1245U (up to 4.4 GHz)
- **RAM**: 16GB
- **OS**: Ubuntu 22.04 LTS

Performance will vary based on hardware, but relative characteristics should remain consistent.

## Troubleshooting

### Error: "rustc 1.81 or newer required"

Update your Rust installation:

```bash
rustup update stable
rustup default stable
rustc --version  # Verify version
```

### Error: "lock file version 4 requires `-Znext-lockfile-bump`"

Your Rust version is too old. Update to Rust 1.81 or newer (see above).

### Error: "command 'rustup' not found"

Install rustup following the instructions in the [Installation](#installation) section.

### Build Failures

Ensure:
1. ✅ Rust 1.81 or newer installed (`rustc --version`)
2. ✅ In correct directory (`cd shuflle_proof_test`)
3. ✅ Internet connection available (for dependencies)
4. ✅ Sufficient disk space (~500MB)

### Benchmarks Running Slowly

Benchmarks are computationally intensive. The `cargo bench` command automatically uses release mode for optimal performance. Runtime depends on hardware specifications.

### Verificatum: Port Already in Use

If you encounter errors about ports being in use when running Verificatum benchmarks:

**Symptom**:
```
java.net.BindException: Address already in use
```

**Solution**:
This issue can occur if your hostname contains special characters or hyphens. Change your hostname to `localhost`:

```bash
# Temporary fix (until reboot)
sudo hostnamectl set-hostname localhost
```

For more details, see: https://github.com/verificatum/verificatum-vmn/issues/17

## Available Benchmark Files

To see all available benchmarks:

```bash
ls benches/
```

Output should show:
- `quick.rs` - Quick validation
- `table1.rs` - Paper Table 1
- `table2.rs` - Paper Table 2
- `r1cs.rs` - Custom parameters
- `verificatum_benchmark.sh` - Verificatum comparison

## License

This project is licensed under the MIT License. See [LICENSE.txt](LICENSE.txt) for details.

## Citation

If you use this code in your research, please cite the associated paper.

## Contact

For questions or issues, please open an issue on the GitHub repository.
