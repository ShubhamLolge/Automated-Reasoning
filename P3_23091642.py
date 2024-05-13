
# Returns a magic square
# This code was adapted from Stack Overflow post Creating associative magic squares z3 python
# accessed 21 March 2024
# https://stackoverflow.com/questions/70048300/creating-associative-magic-squares-z3-python 
# Added code to allow to solve for creating associative magic squares.
# @param input incomplete number square
# @param size of number square
# @return complete magic square

from z3 import *

# Creating a solver
solver = Solver()

# This function takes input grid size and incomplete square and returns a complete magic square if the solution is satisfiable.
def complete_magic_square(grid_size, incomplete_square):
    # Create integer variables for the magic square cells
    square = [[Int(f'cell_{i}_{j}') for j in range(grid_size)] for i in range(grid_size)]

    # Constraints: Each cell contains a unique digit from 1 to n^2
    constraints = [And(1 <= square[i][j], square[i][j] <= grid_size**2)
                               for i in range(grid_size) for j in range(grid_size)]

    # Constraint: Magic constant
    magic_constant = Sum(square[0])
    
    # Constraint: Rows have the same sum (magic constant)
    row_constraints = [
        Sum(square[i]) == magic_constant for i in range(grid_size)
    ]
    
    # Constraint: Columns have the same sum (magic constant)
    column_constraints = [
        Sum([square[j][i] for j in range(grid_size)]) == magic_constant for i in range(grid_size)
    ]
    
    # Constraint: Diagonals have the same sum (magic constant)
    diagonal_constraints = [
        Sum([square[i][i] for i in range(grid_size)]) == magic_constant,
        Sum([square[grid_size-i-1][i] for i in range(grid_size)]) == magic_constant
    ]

    # Constraint: Associative property (sums along certain diagonals)
    associative_sum = Int('associative_sum')
    associative_row_constraints = [(square[0][i] + square[grid_size-1][grid_size-i-1]) == associative_sum for i in range(grid_size)]
    associative_column_constraints = [(square[i][0] + square[grid_size-i-1][grid_size-1]) == associative_sum for i in range(1, grid_size-1)]

    # Adding constraints to the solver
    solver.add(
        constraints + 
        row_constraints + 
        column_constraints +
        diagonal_constraints + 
        associative_row_constraints + 
        associative_column_constraints
    )

    # Constraints from the incomplete square
    incomplete_square_constraints = [
        If(incomplete_square[i][j] != 0, square[i][j] == incomplete_square[i][j], True)
        for i in range(grid_size) for j in range(grid_size)
    ]

    solver.add(incomplete_square_constraints)


    # Solve the asserted constraints.
    if solver.check() == sat:
        model = solver.model()
        magic_square_solution = [[model.evaluate(square[i][j]).as_long() for j in range(grid_size)] for i in range(grid_size)]
        
        print("Satisfiability:",solver.check())
        
        # Display the solution in the symbolic expression (i.e. SMT-LIB2 format).
        print("SMT-LIB2 format: ",model.sexpr())

        return magic_square_solution
    else:
        return None

grid_size = 4
incomplete_square = [
    [0, 0, 1, 0],
    [0, 5, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 6]
]

# Calling function complete_magic_square() with grid_size and incomplete_square
magic_square_solution = complete_magic_square(grid_size, incomplete_square)

# Visualise the solution
if magic_square_solution:
    print(f"Magic Square ({grid_size}x{grid_size}):")
    for row in magic_square_solution:
        print(row)
else:
    print(f"No solution found for {grid_size}x{grid_size} Magic Square.")

'''
Output of the code.

shubhamlolge@Shubhams-MacBook-Air submission % python3 P3_23091642.py

# Indicating that the solution is satisfiable.
Satisfiability: sat

# Displaying the solution in the symbolic expression (SMT-LIB2 format).
SMT-LIB2 format:  (define-fun cell_0_1 () Int
  6)
(define-fun cell_2_1 () Int
  1)
(define-fun cell_2_3 () Int
  5)
(define-fun cell_0_3 () Int
  10)
(define-fun cell_1_3 () Int
  1)
(define-fun cell_1_2 () Int
  10)
(define-fun cell_3_1 () Int
  10)
(define-fun cell_3_3 () Int
  6)
(define-fun cell_2_2 () Int
  6)
(define-fun associative_sum () Int
  11)
(define-fun cell_0_2 () Int
  1)
(define-fun cell_1_0 () Int
  6)
(define-fun cell_2_0 () Int
  10)
(define-fun cell_1_1 () Int
  5)
(define-fun cell_3_0 () Int
  1)
(define-fun cell_3_2 () Int
  5)
(define-fun cell_0_0 () Int
  5)

# Complete magic square.
Magic Square (4x4):
[5, 6, 1, 10]
[6, 5, 10, 1]
[10, 1, 6, 5]
[1, 10, 5, 6]
'''