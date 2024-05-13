# Automated-Reasoning
Solving problems using Z3Py.

### scheduling problem   

Z3Py code to solve the scheduling problem is given as follows. There are seven jobs #1, #2, #3, #4, #5, #6 and #7. All jobs are executed by three people A, B, and C. Solutions of the scheduling problem must satisfy all of the following constraints.

* Each job should be executed by one of three persons A, B, and C without interruption.
* Each person can handle at most one job each time.
* Each job #𝑖 has running time 3 + 𝑖 if person C executes it, and 4 + 𝑖 otherwise.
* Only person B is allowed to execute jobs #1 and #7.
* Job #2 should run after jobs #5 and #6 have finished.
* Each job should be done in time 0 to 20.

Declare only three functions whose domains and ranges are both the set of integers.

* Function S maps each job to its start time.
* Function E maps each job to its end time.
* Function P maps each job to the person who executes it.

----
   
### Crash Me   

Z3Py code to establish the possibility that the following program causes a crash.

<img width="240" alt="Screenshot 2024-05-13 at 8 57 15 PM" src="https://github.com/ShubhamLolge/Uni-Automated-Reasoning/assets/75387392/07f9436a-fc77-498e-8f57-56c23a400913">

Here, ‘←’ is an assignment operator, and ‘?1’ and ‘?2’ are unknown tests that may yield false or true in any situation.

Example crash demo

𝑎 = [1, 2, 3, 3, 3, 17, 22, 28, 35, 134, 143, 153, 153, 570, 583, 597]   
𝑏 = [1, 1, 4, 8, 14, 14, 36, 64, 99, 99, 242, 395, 417, 417, 1000, 1597]   


----


### Magic Square   

Solve the magic squares problem using Z3Py, the task is to construct a magic square, given an incomplete N x N number grid square.   

-----
