#!/usr/bin/env python3
"""
File: get_tags.py

Author: Santiago Cuellar
Date: Apr 25, 2024

Usage:
    usage: get_tags.py [-h] [-v] [-o OUT]
    
    Scan directories and process tags and categories.
    
    options:
      -h, --help         show this help message and exit
      -v, --verbose      print output to standard output as well as writing to file
      -o OUT, --out OUT  specify the output file name

Description:
    This module is designed to scan through directories containing C code files,
    extract tags from specific comment patterns, and categorize files based on their directory structure.
    It compiles a reverse lookup table where each tag is associated with a list of files that contain it,
    as well as a categorization of files based on predefined error types and statuses.

    Example:
        To run this module, execute the main function after setting the directory variable
        to the root directory where the C files are stored:
            `python get_tags.py`

Functions:
    find_c_files(directory) -> generator:
        Yields paths of C files found in the given directory recursively.

    extract_tags(file_path) -> dict:
        Extracts tags from a given C file and returns a dictionary of tags and corresponding file paths.

    categorize_file(file_path) -> str:
        Determines the category of a file based on its directory path, see README for details.

    compile_tag_table(directory) -> tuple:
        Compiles a table of tags and corresponding files and a dictionary of categories and files.

    gather_output(directory) -> output:
        Calls compile_tag_table and formats data about tags and categories into a list of strings to be printed.

    main():
        Sets the base directory, runs the compilation of tags and categories, and prints the results.

"""


import os
import re
import argparse

def categorize_file(file_path):
    """
    Determine the category of the file based on its directory path by stripping the source directory
    and the filename, then matching the remaining path against known categories.
    
    Args:
        file_path (str): Path to the C file.
    
    Returns:
        str: Category of the file based on the remaining directory path after stripping the source and filename.
    """
    # Normalize the path to remove any relative components
    normalized_path = os.path.normpath(file_path)
    
    # Split the path into parts
    parts = normalized_path.split(os.sep)
    
    # Check if the path has at least three parts (minimum required for a source, a category, and a filename)
    if len(parts) < 3:
        return 'Uncategorized'  # Not enough parts to categorize
    
    # Remove the first element (source directory) and the last element (filename)
    category_parts = parts[1:-1]  # This slices out the source and the file name
    
    # Join the parts back to form the category path
    category_path = '/'.join(category_parts)
    
    # Define known categories
    known_categories = {
        'inprogress': 'Uncategorized',
        'working': 'Working',
        'broken/error-cerberus': 'Error Cerberus',
        'broken/error-crash': 'Error Crash',
        'broken/error-proof': 'Error Proof',
        'broken/error-timeout': 'Error Timeout'
    }
    
    # Return the corresponding category if it exists in the known categories
    # if category_path not in known_categories:
    #     print(category_path, "failed!")
    return known_categories.get(category_path, 'Wrongly Filled. See README.')


def find_c_files(directory):
    """Recursively find all .c files in the specified directory."""
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith('.c'):
                yield os.path.join(root, file)

def extract_tags(file_path):
    """Extract tags from a given C file."""
    tags = set()  # Initialize an empty set for tags
    with open(file_path, 'r', encoding='utf-8') as file:
        content = file.readlines()
    tag_regex = re.compile(r'// Tags: (.*)')
    for line in content:
        match = tag_regex.search(line)
        if match:
            # Split the matched group by commas and strip whitespace, then add to the set
            tags.update(tag.strip() for tag in match.group(1).split(','))
    return tags

def compile_tag_table(directory):
    """Compile a table of categories, tags, and the corresponding files."""
    all_tags = {}
    categories = {}
    for file_path in find_c_files(directory):
        category = categorize_file(file_path)

        # Add file to its category
        if category in categories:
            categories[category].append(file_path)
        else:
            categories[category] = [file_path]
        
        file_tags = extract_tags(file_path)

        # Add file to tags
        for tag in file_tags:
            if tag in all_tags:
                all_tags[tag].append(file_path)
            else:
                all_tags[tag] = [file_path]    
    return all_tags, categories
		
def gather_output(directory):
    tag_table, category_table = compile_tag_table(directory)
    output = []  # List to collect output

    # Collect tags information
    output.append('\n' + "-" * 80)
    output.append("Tags:")
    output.append("-" * 80)
    for tag, files in sorted(tag_table.items()):
        output.append(f"{tag}:")
        for file in set(files):
            output.append(f"    {file}")

    # Collect categories information
    output.append('\n' + "-" * 80)
    output.append("Categories:")
    output.append("-" * 80)
    for category, files in sorted(category_table.items()):
        output.append(f"{category}:")
        quant = len(files)
        print(f"\t{category}: [{quant}]" )
        for file in set(files):
            output.append(f"    {file}")

    return output

def main():
    # Argument parsing setup
    parser = argparse.ArgumentParser(description="Scan directories and process tags and categories.")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="print output to standard output as well as writing to file")
    parser.add_argument("-o", "--out", type=str, default="examples_summary.md",
                        help="specify the output file name")

    args = parser.parse_args()

    # Setting the output file name from arguments
    output_filename = args.out

    # Gathering output from a function (assuming gather_output is defined and works as before)
    output = gather_output('.')  # Assuming '.' is your directory

    # Output processing
    with open(output_filename, 'w') as f:
        for line in output:
            f.write(line + '\n')
            if args.verbose:
                print(line)

    print (f"\nSummary of examples and tags written to {output_filename}\n")


if __name__ == "__main__":
    main()
