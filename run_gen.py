import bin.syntax_check as syntax_check
import subprocess
import os

"""
Run Ocaml project to generate benchmar expressions
"""
                      
def build_ocaml_program():
    """
    Run the OCaml program and save its output to a file.
    """
    try:
        print("Building OCaml project...")
        # Run the OCaml program and capture its output
        result = subprocess.run(
            ["dune", "build"],
            cwd="./bin",
            capture_output=True,
            text=True,
            check=True
        )
        print("Build successful!")

    except subprocess.CalledProcessError as e:
        print(f"Error running OCaml program: {e}")
        raise

def execute(args):
    """input arguments input indicating parameters for generation
    1: exp_max_size
    2: bexp_max_size
    3: max_p_bool_count
    4: bench_count_eq
    5: counter_equal
    6: path
"""

    try:

        process = subprocess.run(
            ["dune", "exec", "bench"] + args,
            cwd="./bin",
             stdout=subprocess.PIPE,
             stderr=subprocess.PIPE,
             text=True)

    except Exception as e:
        print(f"Error executing bench in myKAT/bin: {e}")
        return None


def main():
    """input should be in this format = e2000b20p200"""

    benchmark = "e3000b30p200" #input("Enter benchamrk in eXXXbYYYpZZZ format:")

    # Get the current directory of the script
    current_dir = os.path.dirname(__file__)
    
    # Construct the directpry benchmark path
    bench_directory_path = os.path.join(current_dir, benchmark + "eq")

    # Path to save the generated expressions
    output_file_path = bench_directory_path

    build_ocaml_program()

    exp_max_size = 6000
    bexp_max_size = 30
    max_p_bool_count = 200
    bench_count_eq = 50
    counter_equal = 0 #starting point file
    path = "../" + benchmark

    args = [
        str(exp_max_size),
        str(bexp_max_size),
        str(max_p_bool_count),
        str(bench_count_eq),
        str(counter_equal),
        path
    ]

    execute(args)

    return syntax_check.process_bench(benchmark)

    """# Read and check the generated expressions
    try:
        expr1, expr2, status = syntax_check.read_expressions_from_file(output_file_path)

        # Test syntactic equality
        if expr1 == expr2:
            print("The expressions are syntactically the same.")
            print("Reproducing the expressions ...")

        else:
            print("The expressions are NOT syntactically the same.")
    
    except Exception as e:
        print(f"Error: {e}")"
        
        """

if __name__ == "__main__":
    main()
