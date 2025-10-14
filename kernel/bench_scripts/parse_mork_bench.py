import re
import csv
import sys
import argparse

def parse_benchmark_output(text):
    """Parse benchmark output and extract test names and execution times."""
    
    # Define the benchmark names we're looking for
    benchmarks = [
        '3-clique',
        '4-clique',
        '5-clique',
        'counter_machine',
        'exponential',
        'exponential_fringe',
        'finite_domain',
        'odd_even_sort',
        'process_calculus',
        'transitive_trans',
        'transitive_detect'
    ]
    
    results = {}
    
    # Initialize all benchmarks
    for bench in benchmarks:
        results[bench] = []
    
    # Pattern to match time measurements in microseconds
    time_pattern = r'(\d+)\s+µs'
    # Pattern to match elapsed time (not in µs)
    elapsed_pattern = r'elapsed\s+(\d+)'
    
    lines = text.split('\n')
    current_benchmark = None
    
    for i, line in enumerate(lines):
        # Track which benchmark section we're in
        if '=== benchmarking' in line:
            if 'counter_machine' in line:
                current_benchmark = 'counter_machine'
            elif 'exponential_fringe' in line:
                current_benchmark = 'exponential_fringe'
            elif 'exponential' in line and 'fringe' not in line:
                current_benchmark = 'exponential'
            elif 'odd_even_sort' in line:
                current_benchmark = 'odd_even_sort'
            else:
                current_benchmark = None
        
        # Check for specific clique queries
        if '3-clique' in line and i+1 < len(lines) and 'found' in lines[i+1]:
            matches = re.findall(time_pattern, lines[i+1])
            if matches:
                results['3-clique'].append(int(matches[0]))
        elif '4-clique' in line and i+1 < len(lines) and 'found' in lines[i+1]:
            matches = re.findall(time_pattern, lines[i+1])
            if matches:
                results['4-clique'].append(int(matches[0]))
        elif '5-clique' in line and i+1 < len(lines) and 'found' in lines[i+1]:
            matches = re.findall(time_pattern, lines[i+1])
            if matches:
                results['5-clique'].append(int(matches[0]))
        
        # Check for elapsed times in specific benchmarks
        if current_benchmark in ['counter_machine', 'exponential', 'exponential_fringe', 'odd_even_sort']:
            matches = re.findall(elapsed_pattern, line)
            if matches:
                results[current_benchmark].append(int(matches[0]))
        
        # Check for finite_domain
        if '(10000 inputs) in' in line:
            matches = re.findall(time_pattern, line)
            if matches:
                results['finite_domain'].append(int(matches[0]))
        
        # Check for process_calculus
        if '(1000 steps) in' in line:
            matches = re.findall(time_pattern, line)
            if matches:
                results['process_calculus'].append(int(matches[0]))
        
        # Check for transitive benchmarks - only the two with elapsed times
        if 'trans elapsed' in line and 'detect' not in line:
            matches = re.findall(time_pattern, line)
            if matches:
                results['transitive_trans'].append(int(matches[0]))
        elif 'detect trans elapsed' in line:
            matches = re.findall(time_pattern, line)
            if matches:
                results['transitive_detect'].append(int(matches[0]))
    
    return results, benchmarks

def write_to_csv_multi(all_results, benchmarks, output_file=None, to_stdout=False):
    """Write parsed results from multiple files to a CSV file or stdout."""
    
    # Prepare CSV content
    csv_rows = []
    
    # Write header
    header = []
    for bench in benchmarks:
        count = max(len(results.get(bench, [])) for results in all_results)
        if count == 0:
            header.append(bench)
        elif count == 1:
            header.append(bench)
        else:
            for i in range(count):
                header.append(f'{bench}_{i+1}')
    csv_rows.append(header)
    
    # Write data rows (one per input file)
    for file_idx, results in enumerate(all_results):
        row = []
        for bench in benchmarks:
            times = results.get(bench, [])
            if len(times) == 0:
                # Determine how many columns this benchmark needs
                max_count = max(len(r.get(bench, [])) for r in all_results)
                if max_count == 0:
                    row.append('')
                else:
                    row.extend([''] * max_count)
            else:
                row.extend(times)
                # Pad with empty strings if this file has fewer values than others
                max_count = max(len(r.get(bench, [])) for r in all_results)
                if len(times) < max_count:
                    row.extend([''] * (max_count - len(times)))
        csv_rows.append(row)
    
    if to_stdout:
        # Write to stdout
        writer = csv.writer(sys.stdout)
        for csv_row in csv_rows:
            writer.writerow(csv_row)
    else:
        # Write to file
        if output_file is None:
            output_file = 'benchmark_results.csv'
        
        with open(output_file, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            for csv_row in csv_rows:
                writer.writerow(csv_row)
        
        print(f"CSV file '{output_file}' created successfully!")
        print(f"Processed {len(all_results)} input file(s)")
        
        # Print summary
        print("\nExtracted times per file:")
        for file_idx, results in enumerate(all_results):
            print(f"\nFile {file_idx + 1}:")
            for bench in benchmarks:
                times = results.get(bench, [])
                if times:
                    print(f"  {bench}: {times}")
                else:
                    print(f"  {bench}: No time found")

def write_to_csv(results, benchmarks, output_file=None, to_stdout=False):
    """Write parsed results to a CSV file or stdout (single file version)."""
    # This is now a wrapper for backward compatibility
    write_to_csv_multi([results], benchmarks, output_file, to_stdout)

def main():
    parser = argparse.ArgumentParser(description='Parse benchmark output and convert to CSV')
    parser.add_argument('input_files', nargs='+', help='Path(s) to the benchmark output file(s)')
    parser.add_argument('-o', '--output', help='Output CSV file (default: benchmark_results.csv)')
    parser.add_argument('--stdout', action='store_true', help='Output CSV to stdout instead of file')
    
    args = parser.parse_args()
    
    # Parse all input files
    all_results = []
    benchmarks = None
    
    for input_file in args.input_files:
        try:
            with open(input_file, 'r') as f:
                benchmark_text = f.read()
        except FileNotFoundError:
            print(f"Error: File '{input_file}' not found", file=sys.stderr)
            sys.exit(1)
        except Exception as e:
            print(f"Error reading file '{input_file}': {e}", file=sys.stderr)
            sys.exit(1)
        
        # Parse the file
        results, file_benchmarks = parse_benchmark_output(benchmark_text)
        all_results.append(results)
        
        # Use the first file's benchmark list for all
        if benchmarks is None:
            benchmarks = file_benchmarks
    
    # Write to CSV with multiple rows
    write_to_csv_multi(all_results, benchmarks, output_file=args.output, to_stdout=args.stdout)

if __name__ == "__main__":
    main()