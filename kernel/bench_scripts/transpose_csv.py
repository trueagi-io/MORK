#!/usr/bin/env python3

import pandas as pd
import argparse
import os
import sys
from pathlib import Path

def transpose_csv_column(directory, column_name, output_file=None):
    """
    Transpose a specific column from multiple CSV files into a single output CSV.
    
    Args:
        directory: Directory containing CSV files
        column_name: Name of column to extract from each file
        output_file: Output CSV filename (default: <column_name>.csv)
    
    Returns:
        DataFrame with transposed columns
    """
    # Find all CSV files in directory
    csv_files = sorted(Path(directory).glob('*.csv'))
    
    if not csv_files:
        print(f"No CSV files found in directory: {directory}", file=sys.stderr)
        sys.exit(1)
    
    print(f"Found {len(csv_files)} CSV file(s) in {directory}")
    
    # Dictionary to store columns from each file
    columns_data = {}
    skipped_files = []
    
    for csv_file in csv_files:
        try:
            df = pd.read_csv(csv_file)
            
            # Check if column exists
            if column_name in df.columns:
                # Use filename (without extension) as the new column header
                file_stem = csv_file.stem
                columns_data[file_stem] = df[column_name].values
                print(f"  ✓ {csv_file.name}: extracted column '{column_name}' ({len(df[column_name])} rows)")
            else:
                skipped_files.append(csv_file.name)
                print(f"  ✗ {csv_file.name}: column '{column_name}' not found")
                
        except Exception as e:
            skipped_files.append(csv_file.name)
            print(f"  ✗ {csv_file.name}: error reading file - {e}")
    
    if not columns_data:
        print(f"\nError: Column '{column_name}' not found in any CSV files", file=sys.stderr)
        sys.exit(1)
    
    # Create output DataFrame
    # Find the maximum length among all columns
    max_length = max(len(col) for col in columns_data.values())
    
    # Pad shorter columns with NaN to match max length
    padded_data = {}
    for col_name, col_data in columns_data.items():
        if len(col_data) < max_length:
            padded = list(col_data) + [None] * (max_length - len(col_data))
            padded_data[col_name] = padded
        else:
            padded_data[col_name] = col_data
    
    output_df = pd.DataFrame(padded_data)
    
    # Determine output filename
    if output_file is None:
        output_file = f"{column_name}.csv"
    
    # Write to CSV
    output_df.to_csv(output_file, index=False)
    
    print(f"\n{'='*60}")
    print(f"Successfully created: {output_file}")
    print(f"  Columns: {len(columns_data)}")
    print(f"  Rows: {max_length}")
    if skipped_files:
        print(f"  Skipped files: {len(skipped_files)}")
    print(f"{'='*60}")
    
    return output_df

def main():
    parser = argparse.ArgumentParser(
        description='Transpose a column from multiple CSV files into a single CSV',
        epilog='Example: python transpose_csv.py ./benchmark_outputs 3-clique -o results.csv'
    )
    parser.add_argument('directory', help='Directory containing CSV files')
    parser.add_argument('column_name', help='Name of column to extract from each file')
    parser.add_argument('-o', '--output', help='Output CSV filename (default: <column_name>.csv)')
    
    args = parser.parse_args()
    
    # Check if directory exists
    if not os.path.isdir(args.directory):
        print(f"Error: Directory '{args.directory}' does not exist", file=sys.stderr)
        sys.exit(1)
    
    # Perform transpose
    transpose_csv_column(args.directory, args.column_name, args.output)

if __name__ == "__main__":
    main()
