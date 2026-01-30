#!/bin/bash
# ============================================================================
# Verificatum Shuffle Proof Benchmark Script
# ============================================================================
# This script benchmarks Verificatum's shuffle proof implementation for
# comparison with the Rust implementation in this repository.
#
# Prerequisites:
#   - Verificatum Verificatum Mix-Net (vmn) installed
#   - Java JDK 11 or newer
#   - At least 12GB RAM available
#
# Usage:
#   chmod +x benchmarks/verificatum_benchmark.sh
#   ./benchmarks/verificatum_benchmark.sh
# ============================================================================

# ============================================================================
# JVM Configuration
# ============================================================================
# These settings ensure fair comparison with single-threaded Rust benchmarks

JAVA_OPTS=""
JAVA_OPTS="$JAVA_OPTS -XX:+UseSerialGC"
JAVA_OPTS="$JAVA_OPTS -Xms12G -Xmx12G"
JAVA_OPTS="$JAVA_OPTS -XX:+AlwaysPreTouch"
JAVA_OPTS="$JAVA_OPTS -XX:-TieredCompilation"
JAVA_OPTS="$JAVA_OPTS -XX:CompileThreshold=100"
JAVA_OPTS="$JAVA_OPTS -XX:+UseCompressedOops"
JAVA_OPTS="$JAVA_OPTS -XX:-UseBiasedLocking"
JAVA_OPTS="$JAVA_OPTS -XX:CICompilerCount=2"
JAVA_OPTS="$JAVA_OPTS -Djava.util.concurrent.ForkJoinPool.common.parallelism=1"
JAVA_OPTS="$JAVA_OPTS -Dcom.verificatum.eio.globalParallelism=1"
JAVA_OPTS="$JAVA_OPTS -Dcom.verificatum.arithm.globalParallelism=1"

export JAVA_TOOL_OPTIONS="$JAVA_OPTS"

# Pin to single core
taskset -pc 0 $$ > /dev/null 2>&1

# ============================================================================
# Benchmark Parameters
# ============================================================================

NUM_WARMUP=50
NUM_BENCHMARK=100
TOTAL_RUNS=$((NUM_WARMUP + NUM_BENCHMARK))

# Test values matching Rust benchmarks
N_VALUES=(1024 4096 16384 65536 262144 1048576)

# ============================================================================
# File Paths
# ============================================================================

PRIV_INFO="privInfo.xml"
PROT_INFO="protInfo.xml"
CIPH_FILE="ciphertexts"
PUB_KEY="publicKey"
ERROR_LOG="error_verificatum.log"
RESULTS_DIR="results_$(date +%Y%m%d_%H%M%S)"

mkdir -p "$RESULTS_DIR"

# ============================================================================
# Pre-warm JVM
# ============================================================================

echo "================================================================"
echo " Verificatum Shuffle Proof Benchmark"
echo "================================================================"
echo " Date:         $(date)"
echo " JVM:          $(java -version 2>&1 | head -n 1)"
echo " Heap:         12GB"
echo " Warm-up:      $NUM_WARMUP iterations"
echo " Measurements: $NUM_BENCHMARK iterations"
echo " Results:      $RESULTS_DIR"
echo "================================================================"
echo ""
echo "Pre-warming JVM..."

PRE_WARM_N=256

rm -f "$PRIV_INFO" "$PROT_INFO" "$CIPH_FILE" "$PUB_KEY" localProtInfo.xml stub.xml 2>/dev/null

P256_GROUP_OBJECT=$(vog -gen ECqPGroup -name P-256 2>> "$ERROR_LOG")
if [ -z "$P256_GROUP_OBJECT" ]; then 
    echo "ERROR: Could not generate P-256 group."
    echo "Check that Verificatum is installed correctly."
    exit 1
fi

vmni -prot -sid "PreWarm" -name "PreWarm" -nopart 1 -thres 1 -rohash SHA-512 -pgroup "$P256_GROUP_OBJECT" stub.xml 2>> "$ERROR_LOG"
vmni -party -name "Mix Server 1" stub.xml "$PRIV_INFO" localProtInfo.xml 2>> "$ERROR_LOG"
vmni -merge localProtInfo.xml "$PROT_INFO" 2>> "$ERROR_LOG"
vmn -keygen "$PRIV_INFO" "$PROT_INFO" "$PUB_KEY" 2>> "$ERROR_LOG"
vmnd -ciphs "$PUB_KEY" "$PRE_WARM_N" "$CIPH_FILE" 2>> "$ERROR_LOG"

for i in $(seq 1 20); do
    AUX_SID="prewarm${i}"
    vmn -shuffle -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" "$CIPH_FILE" "prewarm_plain_$i" 2>> "$ERROR_LOG"
    vmn -delete -f -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" 2>> "$ERROR_LOG"
    rm -f "prewarm_plain_$i"
    echo -ne "  Pre-warm $i/20\r"
done
echo "  Pre-warm complete."

rm -f "$PRIV_INFO" "$PROT_INFO" "$CIPH_FILE" "$PUB_KEY" localProtInfo.xml stub.xml

# ============================================================================
# Main Benchmark Loop
# ============================================================================

for CIPHERTEXTS in "${N_VALUES[@]}"; do

    echo ""
    echo "================================================================"
    echo " N = $CIPHERTEXTS"
    echo "================================================================"

    LOG_FILE="$RESULTS_DIR/verificatum_N${CIPHERTEXTS}.csv"
    echo "Iteration,Type,Session_ID,Prover_ms,Verifier_ms,Proof_bytes" > "$LOG_FILE"

    # Setup
    rm -f "$PRIV_INFO" "$PROT_INFO" "$CIPH_FILE" "$PUB_KEY" localProtInfo.xml stub.xml

    P256_GROUP_OBJECT=$(vog -gen ECqPGroup -name P-256 2>> "$ERROR_LOG")
    if [ -z "$P256_GROUP_OBJECT" ]; then 
        echo "ERROR: Setup failed for N=$CIPHERTEXTS"
        continue
    fi

    vmni -prot -sid "SetupN${CIPHERTEXTS}" -name "Benchmark" -nopart 1 -thres 1 -rohash SHA-512 -pgroup "$P256_GROUP_OBJECT" stub.xml 2>> "$ERROR_LOG"
    vmni -party -name "Mix Server 1" stub.xml "$PRIV_INFO" localProtInfo.xml 2>> "$ERROR_LOG"
    vmni -merge localProtInfo.xml "$PROT_INFO" 2>> "$ERROR_LOG"
    vmn -keygen "$PRIV_INFO" "$PROT_INFO" "$PUB_KEY" 2>> "$ERROR_LOG"
    vmnd -ciphs "$PUB_KEY" "$CIPHERTEXTS" "$CIPH_FILE" 2>> "$ERROR_LOG"

    echo "Running $TOTAL_RUNS iterations..."

    for i in $(seq 1 $TOTAL_RUNS); do
        if [ "$i" -le "$NUM_WARMUP" ]; then 
            TYPE="WARMUP"
        else 
            TYPE="BENCHMARK"
        fi

        AUX_SID="session_${CIPHERTEXTS}_${i}"
        PLAIN_FILE="plaintext_${CIPHERTEXTS}_${i}"
        
        # Prover
        PROVER_START=$(date +%s%3N)
        vmn -shuffle -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" "$CIPH_FILE" "$PLAIN_FILE" 2>> "$ERROR_LOG"
        PROVER_END=$(date +%s%3N)
        PROVER_TIME_MS=$((PROVER_END - PROVER_START))
        
        # Measure proof size
        SESSION_PROOF_DIR="dir/nizkp/$AUX_SID"
        if [ -d "$SESSION_PROOF_DIR" ]; then
            PROOF_SIZE_BYTES=$(du -sb "$SESSION_PROOF_DIR" 2>/dev/null | cut -f1)
        else
            PROOF_SIZE_BYTES=0
        fi
        
        # Verifier
        VERIFIER_START=$(date +%s%3N)
        vmn -verify -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" 2>> "$ERROR_LOG"
        VERIFIER_END=$(date +%s%3N)
        VERIFIER_TIME_MS=$((VERIFIER_END - VERIFIER_START))

        echo "$i,$TYPE,$AUX_SID,$PROVER_TIME_MS,$VERIFIER_TIME_MS,$PROOF_SIZE_BYTES" >> "$LOG_FILE"

        vmn -delete -f -auxsid "$AUX_SID" "$PRIV_INFO" "$PROT_INFO" 2>> "$ERROR_LOG"
        rm -rf "$PLAIN_FILE" "$SESSION_PROOF_DIR"
        
        echo -ne "  Progress: $i/$TOTAL_RUNS\r"
    done
    
    echo ""

    # Calculate statistics
    STATS=$(tail -n +$((NUM_WARMUP + 2)) "$LOG_FILE" | awk -F',' '
        $2 == "BENCHMARK" {
            if ($4 ~ /^[0-9]+$/) { psum += $4; pc++; }
            if ($5 ~ /^[0-9]+$/) { vsum += $5; vc++; }
            if ($6 ~ /^[0-9]+$/ && proof_size == 0) { proof_size = $6; }
        }
        END {
            pmean = (pc > 0) ? psum / pc : 0;
            vmean = (vc > 0) ? vsum / vc : 0;
            printf "%.1f,%.1f,%d\n", pmean, vmean, proof_size;
        }
    ')

    PMEAN=$(echo "$STATS" | cut -d',' -f1)
    VMEAN=$(echo "$STATS" | cut -d',' -f2)
    PROOF_SIZE=$(echo "$STATS" | cut -d',' -f3)

    echo "  Prover:     ${PMEAN} ms"
    echo "  Verifier:   ${VMEAN} ms"
    echo "  Proof size: ${PROOF_SIZE} bytes"

    {
        echo ""
        echo "# Summary for N=$CIPHERTEXTS"
        echo "Prover_mean_ms,$PMEAN"
        echo "Verifier_mean_ms,$VMEAN"
        echo "Proof_size_bytes,$PROOF_SIZE"
    } >> "$LOG_FILE"

done

# ============================================================================
# Generate Summary
# ============================================================================

echo ""
echo "================================================================"
echo " Summary"
echo "================================================================"

SUMMARY_FILE="$RESULTS_DIR/summary.csv"
echo "N,Prover_ms,Verifier_ms,Proof_bytes" > "$SUMMARY_FILE"

for CIPHERTEXTS in "${N_VALUES[@]}"; do
    LOG_FILE="$RESULTS_DIR/verificatum_N${CIPHERTEXTS}.csv"
    if [ -f "$LOG_FILE" ]; then
        PMEAN=$(grep "^Prover_mean_ms," "$LOG_FILE" | cut -d',' -f2)
        VMEAN=$(grep "^Verifier_mean_ms," "$LOG_FILE" | cut -d',' -f2)
        PROOF_SIZE=$(grep "^Proof_size_bytes," "$LOG_FILE" | cut -d',' -f2)
        echo "$CIPHERTEXTS,$PMEAN,$VMEAN,$PROOF_SIZE" >> "$SUMMARY_FILE"
    fi
done

echo "Results saved to: $RESULTS_DIR"
echo "Summary: $SUMMARY_FILE"
echo "================================================================"
