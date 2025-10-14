#!/bin/bash

# Sequential command runner with output to separate files
# Usage: ./run_sequential.sh <num_iterations> <command> [args...]

if [ $# -lt 2 ]; then
    echo "Usage: $0 <num_iterations> <command> [args...]"
    echo "Example: $0 5 ./target/release/mork bench all"
    exit 1
fi

NUM_ITERATIONS=$1
shift  # Remove first argument, leaving the command and its args

COMMAND="$@"
OUTPUT_PREFIX="output"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

echo "=========================================="
echo "Sequential Command Runner"
echo "=========================================="
echo "Command: $COMMAND"
echo "Iterations: $NUM_ITERATIONS"
echo "Output files: ${OUTPUT_PREFIX}_${TIMESTAMP}_*.txt"
echo "=========================================="
echo ""

for i in $(seq 1 $NUM_ITERATIONS); do
    OUTPUT_FILE="${OUTPUT_PREFIX}_${TIMESTAMP}_${i}.txt"
    
    echo "[$(date +%H:%M:%S)] Starting iteration $i of $NUM_ITERATIONS..."
    echo "  Output file: $OUTPUT_FILE"
    
    # Run the command and redirect output to file
    $COMMAND > "$OUTPUT_FILE" 2>&1
    EXIT_CODE=$?
    
    if [ $EXIT_CODE -eq 0 ]; then
        echo "  ✓ Completed successfully"
    else
        echo "  ✗ Failed with exit code $EXIT_CODE"
    fi
    
    echo ""
done

echo "=========================================="
echo "All iterations complete!"
echo "Output files:"
ls -lh ${OUTPUT_PREFIX}_${TIMESTAMP}_*.txt
echo "=========================================="
