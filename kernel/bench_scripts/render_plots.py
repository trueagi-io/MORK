#!/usr/bin/env python3

import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from scipy import stats
import argparse

def plot_distribution(csv_file, column_name, label=None, base_color=None, ax=None, y_position=1):
    """
    Plot data points with color gradient based on distance from mean.
    
    Args:
        csv_file: Path to CSV file
        column_name: Name of column to plot
        label: Label for the dataset (defaults to column_name)
        base_color: Base color for the plot (defaults to auto)
        ax: Matplotlib axis object (creates new if None)
        y_position: Y-coordinate for this dataset's horizontal line
    
    Returns:
        ax: The matplotlib axis object
    """
    # Read the CSV
    df = pd.read_csv(csv_file)
    
    if column_name not in df.columns:
        raise ValueError(f"Column '{column_name}' not found in CSV. Available columns: {list(df.columns)}")
    
    # Get the data and remove NaN values
    data = df[column_name].dropna().values
    
    if len(data) == 0:
        raise ValueError(f"No valid data in column '{column_name}'")
    
    # Fit normal distribution
    mu, std = stats.norm.fit(data)
    
    # Create axis if not provided
    if ax is None:
        fig, ax = plt.subplots(figsize=(10, 6))
    
    # Set label
    if label is None:
        label = column_name
    
    # Calculate how far each point is from the mean in terms of standard deviations
    z_scores = np.abs((data - mu) / std)
    
    # Convert z-scores to alpha values (0 to 1)
    # Points at mean (z=0) get alpha=1 (fully opaque)
    # Points far from mean get lower alpha
    # Use exponential decay: alpha = exp(-z^2 / 2) which matches normal distribution shape
    alphas = np.exp(-z_scores**2 / 2)
    
    # Normalize alphas to range [0.2, 1.0] so even distant points are somewhat visible
    alphas = 0.2 + 0.8 * alphas
    
    # Plot all data points at the specified y position
    y_values = np.full_like(data, y_position)
    
    # Plot the data points with varying alpha based on distance from mean
    for i, (x, alpha) in enumerate(zip(data, alphas)):
        ax.scatter(x, y_values[i], alpha=alpha, s=50, color=base_color, 
                  edgecolors='none', zorder=2)
    
    # Add a dummy scatter for the legend
    ax.scatter([], [], alpha=1.0, s=50, color=base_color, 
              label=f'{label} (μ={mu:.1f}, σ={std:.1f})')
    
    # Add vertical line at mean
    ax.axvline(mu, color=base_color, linestyle='--', alpha=0.3, linewidth=1, zorder=1)
    
    # Add shaded region for ±1 standard deviation
    ax.axvspan(mu - std, mu + std, alpha=0.05, color=base_color, zorder=0)
    
    return ax

def main():
    parser = argparse.ArgumentParser(
        description='Plot CSV column data with fitted normal distribution',
        epilog='Example: python plot_dist.py data.csv -c column1 -c column2 --colors blue red'
    )
    parser.add_argument('csv_file', help='Path to CSV file')
    parser.add_argument('-c', '--columns', nargs='+', 
                        help='Column name(s) to plot (default: all columns)')
    parser.add_argument('-l', '--labels', nargs='+', 
                        help='Custom labels for each dataset')
    parser.add_argument('--colors', nargs='+', 
                        help='Colors for each dataset (e.g., blue red green)')
    parser.add_argument('-o', '--output', help='Output file for plot (e.g., plot.png)')
    parser.add_argument('--title', help='Plot title')
    parser.add_argument('--xlabel', default='Value', help='X-axis label')
    
    args = parser.parse_args()
    
    # Read CSV to get all columns if none specified
    df = pd.read_csv(args.csv_file)
    
    # Use all columns if none specified
    if args.columns is None:
        args.columns = list(df.columns)
        print(f"No columns specified. Using all columns: {args.columns}")
    
    # Create the plot with height adjusted for number of datasets
    # Use minimal height per dataset for compact visualization
    height_per_dataset = 0.4  # inches per dataset row (compact)
    fig_height = max(3, len(args.columns) * height_per_dataset + 2.5)  # extra space for legend below
    fig, ax = plt.subplots(figsize=(12, fig_height))
    
    # Generate distinct colors if not provided
    if args.colors:
        colors = args.colors
        if len(colors) < len(args.columns):
            colors = colors + [None] * (len(args.columns) - len(colors))
    else:
        # Use matplotlib's tab10 colormap for distinct colors
        cmap = plt.cm.get_cmap('tab10')
        colors = [cmap(i % 10) for i in range(len(args.columns))]
    
    # Determine labels
    labels = args.labels if args.labels else args.columns
    if len(labels) < len(args.columns):
        labels = labels + [None] * (len(args.columns) - len(labels))
    
    # Plot each column on a separate horizontal line
    for i, col in enumerate(args.columns):
        base_color = colors[i] if colors else None
        label = labels[i] if labels else None
        try:
            # Pass y_position for this dataset (simple integer positions)
            plot_distribution(args.csv_file, col, label=label, base_color=base_color, ax=ax, y_position=i)
        except ValueError as e:
            print(f"Warning: Skipping column '{col}': {e}")
            continue
    
    # Customize plot
    ax.set_xlabel(args.xlabel, fontsize=12)
    ax.set_ylabel('Dataset', fontsize=12)
    ax.set_title(args.title or 'Distribution Comparison', fontsize=14)
    ax.legend(loc='upper center', bbox_to_anchor=(0.5, -0.15), fontsize=10, ncol=3, borderaxespad=0)
    ax.grid(True, alpha=0.3, axis='x')
    
    # Set y-axis - simple integer positions
    num_datasets = len(args.columns)
    ax.set_ylim(-0.5, num_datasets - 0.5)
    ax.set_yticks(range(num_datasets))
    ax.set_yticklabels([labels[i] if labels[i] else args.columns[i] for i in range(num_datasets)])
    
    # Save or show
    if args.output:
        plt.savefig(args.output, dpi=300, bbox_inches='tight')
        print(f"Plot saved to {args.output}")
    else:
        plt.tight_layout()
        plt.show()

if __name__ == "__main__":
    main()