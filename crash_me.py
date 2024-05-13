from z3 import *

# Creating Z3 integer variables for a and b
a = [Int('a_%i' % i) for i in range(16)]
b = [Int('b_%i' % i) for i in range(16)]

# Creating Z3 boolean variables for ‘?1’ and ‘?2’ which are unknown tests that may yield false or true in any situation.
c1 = [Bool('c1_%i' % i) for i in range(16)]
c2 = [Bool('c2_%i' % i) for i in range(16)]

solver = Solver()

# Initializing variables 'a' and 'b' with initial value 1 
# Set the initial values of a[0] and b[0] to 1.
solver.add(a[0] == 1)
solver.add(b[0] == 1)

# Loop condition
# Specify the conditions for each iteration of the loop.
for i in range(15):
    # Use Or() to specify three possible conditions for each iteration:
    # 1. If c1[i] is true, update a[i+1] as a[i] + i and b[i+1] as a[i+1] + b[i].
    # 2. If c2[i] is true (and c1[i] is false), update b[i+1] as b[i] + 2*i and a[i+1] remains the same as a[i].
    # 3. If neither c1[i] nor c2[i] is true, update a[i+1] as a[i] + b[i] and b[i+1] as b[i].
    solver.add(
        Or(
            And(c1[i], a[i+1] == a[i] + i, b[i+1] == a[i+1] + b[i]),
            And(c2[i], Not(c1[i]), b[i+1] == b[i] + 2*i, a[i+1] == a[i]),
            And(Not(c1[i]), Not(c2[i]), a[i+1] == a[i] + b[i], b[i+1] == b[i])
        )
    )

# Crash condition
# Specify the condition for the program to crash, i.e., when value of 'b' or 'b[i]' reaches 1000.
solver.add(b[i] == 1000)

# Check if there's a solution
# Check if the constraints are satisfiable. If not, exit.
if solver.check() == unsat:
    exit()

print("Satisfiability:",solver.check())

# Get the model
m = solver.model()
res_a = [m.evaluate(a[i]).as_long() for i in range(16)]
res_b = [m.evaluate(b[i]).as_long() for i in range(16)]

print("a =", res_a)
print("b =", res_b)

# Find the index where b reaches 1000
# Explanation: Iterate through the values of b to find the index where it reaches 1000.
crash_index = None
for i in range(16):
    if res_b[i] == 1000:
        crash_index = i
        break

print("Index of 'b' where the program crashes:", crash_index)


'''
Output of the code.
shubhamlolge@Shubhams-MacBook-Air submission % python3 P2_23091642.py

# Indicating that the solution is satisfiable.
Satisfiability: sat

# values of 'a'.
a = [1, 2, 3, 5, 14, 18, 45, 51, 51, 59, 59, 228, 397, 409, 422, 436]

# values of 'b'.
b = [1, 1, 4, 9, 9, 27, 27, 78, 92, 151, 169, 169, 169, 578, 1000, 1436]

# Index of list 'b' where the program crashed is 14.
Index of 'b' where the program crashes: 14
'''

