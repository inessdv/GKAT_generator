import os


def remove_spaces(expr):
    """
    remove spaces, tabs, newlines
    """
    return expr.replace(" ", "").replace("\t", "").replace("\n", "")

def read_expressions_from_file(file_path):
    """
    read and separate the two expressions + equiv 0 or 1.
    """
    with open(file_path, 'r') as file:
        content = file.read().strip()

    # Split expressions
    expressions = content.split('\n\n')
    if len(expressions) != 3:
        raise ValueError("file does not contain exactly two expressions and equiv status separated by an empty line.")

    expr1, expr2, status = expressions 

    return remove_spaces(expr1), remove_spaces(expr2), status  # Remove any extra whitespace


def process_directory(directory_path):
    """
    process all .txt files in the directory and test syntax equality
    """
    # list of all .txt files in the directory
    txt_files = [f for f in os.listdir(directory_path) if f.endswith('.txt')]

    if not txt_files:
        print(f"No .txt files found in directory: {directory_path}")
        return

    results = []
    same_count = 0
    for file_name in txt_files:
        file_path = os.path.join(directory_path, file_name)
        try:
            # Read and separate the expressions and status
            expr1, expr2, _ = read_expressions_from_file(file_path)
            e1_while_0 = expr1.count("while0")
            e2_while_0 = expr2.count("while0")

            # Test syntactic equality
            is_same = (expr1 == expr2)
            if is_same:
                same_count += 1

            results.append((file_name, is_same,e1_while_0, e2_while_0 ))

            # Print result for this file
            print(f"File: {file_name}")
            print(f"Expressions are syntactically the same: {is_same}")
            print(f"E1_while0_count: {e1_while_0}")
            print(f"E2_while0_count: {e2_while_0}")
            print("-" * 40)

        except Exception as e:
            print(f"Error processing file '{file_name}': {e}")
            results.append((file_name, "ERROR", "N/A"))

    # Print summary table
    print("Table results for " + directory_path)
    print("{:<20} {:<15}{:<20}{:<20}".format("File", "Same Syntax", "E1_while0_count","E2_while0_count" ))
    print("-" * 55)
    for file_name, is_same, e1_while_0, e2_while_0 in results:
        print("{:<20} {:<15}{:<20}{:<20}".format(file_name, str(is_same),str(e1_while_0),str(e2_while_0)))
     
    print("Total count of EQUAL SYNTAX Pairs : " + str(same_count))
    
    return results # list of file_name, is_same, e1_while_0, e2_while_0


# Main script
def process_bench(benchmark):
    # Get the current directory of the script
    current_dir = os.path.dirname(__file__)

    parent_dir = os.path.dirname(current_dir)

    # Construct the file path
    directory_path = os.path.join(parent_dir, benchmark +"eq")

    results = process_directory(directory_path)
    
    return results

def main():
    # Get the current directory of the script
    current_dir = os.path.dirname(__file__)

    parent_dir = os.path.dirname(current_dir)

    # Construct the file path
    directory_path = os.path.join(parent_dir, "e3000b30p200eq")

    results = process_directory(directory_path)
    
    return results

if __name__ == "__main__":
    main()