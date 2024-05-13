from z3 import *

# Define Z3 solver
solver = Solver()

# Define Functions
S = Function('S', IntSort(), IntSort())  # Start time of each job
E = Function('E', IntSort(), IntSort())  # End time of each job
P = Function('P', IntSort(), IntSort())  # Person assigned to each job

jobs = [1, 2, 3, 4, 5, 6, 7]
persons = ['A', 'B', 'C']

for job in jobs:
    solver.add(And(S(job) >= 0, S(job) <= 20))  # Start time constraint
    solver.add(And(E(job) >= 0, E(job) <= 20))  # End time constraint
    solver.add(Or([P(job) == persons.index(person) for person in persons]))  # Person constraint
    solver.add(E(job) == S(job) + If(P(job) == 2, 3 + job, 4 + job))  # End time calculation

# Each person can handle at most one job at a time
for person in range(len(persons)):
    jobs_handled_by_person = [job for job in jobs if P(job) == person]
    solver.add(
        sum(
            [
                If(And(S(job2) < E(job1), S(job1) < E(job2)), 1, 0) 
                    for job1 in jobs_handled_by_person for job2 in jobs_handled_by_person if job1 != job2
            ]
        ) <= 1
    )

# Only person B is allowed to execute jobs #1 and #7
solver.add(P(1) == 1)  # Only person B (index 1) can handle job 1 
solver.add(P(7) == 1)  # Only person B (index 1) can handle job 7

# Job #2 should run after jobs #5 and #6 have finished
solver.add(S(2) >= E(5))
solver.add(S(2) >= E(6))

# Solve the asserted constraints.
r = solver.check()

# Exit from the program if unsatisfiable.
if r == unsat:
    exit()

print("Satisfiability:",solver.check())

# Print all constraints.
print(solver)

# Return a solution
model = solver.model()

# Display the solution in the symbolic expression (i.e. SMT-LIB2 format).
print(model.sexpr())

for job in jobs:
    person_index = model.eval(P(job)).as_long()
    person = persons[person_index]
    start_time = model.eval(S(job)).as_long()
    end_time = model.eval(E(job)).as_long()
    print(f"Job #{job} is executed by person {person}, from time {start_time}, to time {end_time}")

# constraints considered.
# • Each job should be executed by one of three persons A, B and C without interruption. ✓
# • Each person can handle at most one job each time. ✓
# • Each job #𝑖 has running time 3 + 𝑖 if person C executes it, and 4 + 𝑖 otherwise. ✓
# • Only person B is allowed to execute jobs #1 and #7. ✓
# • Job #2 should run after jobs #5 and #6 have finished. ✓
# • Each job should be done in time 0 to 20. ✓

'''
Output of the code


shubhamlolge@Shubhams-MacBook-Air submission % python3 P1_23091642.py

# Indicating that the solution is satisfiable.
Satisfiability: sat

# Displaying the solution in the symbolic expression (SMT-LIB2 format).
[And(S(1) >= 0, S(1) <= 20),
 And(E(1) >= 0, E(1) <= 20),
 Or(P(1) == 0, P(1) == 1, P(1) == 2),
 E(1) == S(1) + If(P(1) == 2, 4, 5),
 And(S(2) >= 0, S(2) <= 20),
 And(E(2) >= 0, E(2) <= 20),
 Or(P(2) == 0, P(2) == 1, P(2) == 2),
 E(2) == S(2) + If(P(2) == 2, 5, 6),
 And(S(3) >= 0, S(3) <= 20),
 And(E(3) >= 0, E(3) <= 20),
 Or(P(3) == 0, P(3) == 1, P(3) == 2),
 E(3) == S(3) + If(P(3) == 2, 6, 7),
 And(S(4) >= 0, S(4) <= 20),
 And(E(4) >= 0, E(4) <= 20),
 Or(P(4) == 0, P(4) == 1, P(4) == 2),
 E(4) == S(4) + If(P(4) == 2, 7, 8),
 And(S(5) >= 0, S(5) <= 20),
 And(E(5) >= 0, E(5) <= 20),
 Or(P(5) == 0, P(5) == 1, P(5) == 2),
 E(5) == S(5) + If(P(5) == 2, 8, 9),
 And(S(6) >= 0, S(6) <= 20),
 And(E(6) >= 0, E(6) <= 20),
 Or(P(6) == 0, P(6) == 1, P(6) == 2),
 E(6) == S(6) + If(P(6) == 2, 9, 10),
 And(S(7) >= 0, S(7) <= 20),
 And(E(7) >= 0, E(7) <= 20),
 Or(P(7) == 0, P(7) == 1, P(7) == 2),
 E(7) == S(7) + If(P(7) == 2, 10, 11),
 True,
 True,
 True,
 P(1) == 1,
 P(7) == 1,
 S(2) >= E(5),
 S(2) >= E(6)]
(define-fun P ((x!0 Int)) Int
  (ite (= x!0 1) 1
  (ite (= x!0 7) 1
    2)))
(define-fun S ((x!0 Int)) Int
  (ite (= x!0 2) 9
    0))
(define-fun E ((x!0 Int)) Int
  (ite (= x!0 2) 14
  (ite (= x!0 3) 6
  (ite (= x!0 4) 7
  (ite (= x!0 5) 8
  (ite (= x!0 6) 9
  (ite (= x!0 7) 11
    5)))))))

# Displaying the jobs executed by people
Job #1 is executed by person B, from time 0, to time 5
Job #2 is executed by person C, from time 9, to time 14
Job #3 is executed by person C, from time 0, to time 6
Job #4 is executed by person C, from time 0, to time 7
Job #5 is executed by person C, from time 0, to time 8
Job #6 is executed by person C, from time 0, to time 9
Job #7 is executed by person B, from time 0, to time 11
'''

'''
Running time '3 + i' if 'person C' executes it, and '4 + i' otherwise

4 + i   =   4 + 1  =  5  for person B.
3 + i   =   3 + 2  =  14 for person C. # job #2 has been executed after job #5 and #6.
3 + i   =   3 + 3  =  6  for person C.
3 + i   =   3 + 4  =  7  for person C.
3 + i   =   3 + 5  =  8  for person C.
3 + i   =   3 + 6  =  9  for person C.
4 + i   =   4 + 7  =  11 for person B.
'''

