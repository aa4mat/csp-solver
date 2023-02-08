# =============================
# Student Names:
# Group ID:
# Date:
# =============================
# CISC 352 - W23
# cagey_csp.py
# desc:
#

from itertools import product, permutations

# Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of
Variable objects (cage) representing the board.

The returned list of lists is used to access the solution.

For example, after these three lines of code

    csp, var_array = binary_ne_grid(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array is a list of all variables in the given csp. If you are returning an
entire grid's worth of variables they should be arranged linearly,
where index 0 represents the top left grid cell, index n-1 represents the
top right grid cell, and index (n^2)-1 represents the bottom right grid cell.
Any additional variables you use should fall after that
(i.e., the cage operand variables, if required).

1. binary_ne_grid (worth 10/100 marks)
    - A model of a Cagey grid (without cage constraints) built using only
      binary not-equal constraints for both the row and column constraints.

      for all squares (xi, xj), xi != xk, k ≤ n loops over j
      AND
      for all (xi, xj), xk != xj, k ≤ n over i.


2. nary_ad_grid (worth 10/100 marks)
    - A model of a Cagey grid (without cage constraints) built using only n-ary
      all-different constraints for both the row and column constraints.

3. cagey_csp_model (worth 20/100 marks)
    - a model of a Cagey grid built using your choice of (1) binary not-equal, or
      (2) n-ary all-different constraints for the grid, together with Cagey cage
      constraints.


Cagey Grids are addressed as follows (top number represents how the grid cells
are addressed in grid definition tuple);
(bottom number represents where the cell would fall in the var_array) (<-index):
+-------+-------+-------+-------+
|  1,1  |  1,2  |  ...  |  1,n  |
|       |       |       |       |
|   0   |   1   |       |  n-1  |
+-------+-------+-------+-------+
|  2,1  |  2,2  |  ...  |  2,n  |
|       |       |       |       |
|   n   |  n+1  |       | 2n-1  |
+-------+-------+-------+-------+
|  ...  |  ...  |  ...  |  ...  |
|       |       |       |       |
|       |       |       |       |
+-------+-------+-------+-------+
|  n,1  |  n,2  |  ...  |  n,n  |
|       |       |       |       |
|n^2-n-1| n^2-n |       | n^2-1 |
+-------+-------+-------+-------+

Boards are given in the following format:
(n, [cages])

n - is the size of the grid,
cages - is a list of tuples defining all cage constraints on a given grid.


each cage has the following structure
(v, [c1, c2, ..., cm], op)

v - the value of the cage. (target value - one constraint)
[c1, c2, ..., cm] - is a list containing the address of each grid-cell which goes into the cage (e.g [(1,2), (1,1)])
op - a flag containing the operation used in the cage (None if unknown)
      - '+' for addition
      - '-' for subtraction
      - '*' for multiplication
      - '/' for division
      - '?' for unknown/no operation given

An example of a 3x3 puzzle would be defined as:
(3, [(3,[(1,1), (2,1)],"+"),(1, [(1,2)], '?'), (8, [(1,3), (2,3), (2,2)], "+"),
(3, [(3,1)], '?'), (3, [(3,2), (3,3)], "+")])

'''

from cspbase import *


def binary_ne_grid(cagey_grid):

    # things to do: construct a binary constraint
    # All constraints:
    # 1. Row: for all values in a row i:
    # scope - var-cell(i,j), for j in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i, j+1)
    # itertools - sat_tuples.add([(1, 2), (2,1), (1, 3), (3, 1) ... n
    # 2. Col: for all values in column i:
    # scope - var-cell(i,j), for i in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i+1,j)
    # iterate - add sat_tuples([(1,2) ...
    # put it all into a CSP

    grid_size = cagey_grid[0]
    csp = CSP("Binary-ne-Cagey", [])    # initialise
    domain = [v for v in range(1, grid_size+1)]

    # initialise Variables, add to CSP
    vars = []
    for i in product(range(1, grid_size+1), repeat=2):
        new_var = Variable(("Cell" + str(i)), domain)
        vars.append(new_var)
        csp.add_var(new_var)

    # create scopes, create row constraint, add to CSP
    for row in range(1, grid_size+1):
        for i in permutations(range(1, grid_size+1), 2):
            # note - make this n for  all_diff?
            names = ["Cell(" + str(row) + ", " + str(i[0]) + ")",
                     "Cell(" + str(row) + ", " + str(i[1]) + ")"]
            scope_temp = []
            for var in vars:   # get Variable that matches name, to add to scope
                # NOTE - creating a new variable won't work because matching
                # done by object, not by Variable name
                if var.name in names:
                    scope_temp.append(var)   # 2 values

            scope = [scope_temp[0], scope_temp[1]]
            cons = Constraint("Bin-ne-Cell(" + str(row) + str(i[0]) + "), " +
                              "Cell(" + str(row) + str(i[1]) + ")", scope)

            sat_tuple = [tup for tup in permutations(range(1, grid_size+1), 2)]
            cons.add_satisfying_tuples(sat_tuple)
            csp.add_constraint(cons)

    # create scopes, create column constraint, add to CSP
    for col in range(1, grid_size + 1):
        for i in permutations(range(1, grid_size + 1), 2):
            # note - make this n for  all_diff?
            names = ["Cell(" + str(i[0]) + ", " + str(col) + ")",
                     "Cell(" + str(i[1]) + ", " + str(col) + ")"]
            scope_temp = []
            for var in vars:  # get Variable that matches name, to add to scope
                # NOTE - creating a new variable won't work because matching
                # done by object, not by Variable name
                if var.name in names:
                    scope_temp.append(var)  # 2 values

            scope = [scope_temp[0], scope_temp[1]]
            # if we maintained a list of scopes, we could cut the constraints in
            # half as C(x,y) == C(y,x)
            cons = Constraint(
                "Bin-ne-Cell(" + str(i[0]) + str(col) + "), " +
                "Cell(" + str(i[1]) + str(col) + ")", scope)

            sat_tuple = [tup for tup in
                         permutations(range(1, grid_size + 1), 2)]
            cons.add_satisfying_tuples(sat_tuple)
            csp.add_constraint(cons)

    return csp, []  # right now we don't care about the grid


def nary_ad_grid(cagey_grid):
    # things to do: construct a binary constraint
    # All constraints:
    # 1. Row: for all values in a row i:
    # scope - var-cell(i,j), for j in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i, j+1)
    # itertools - sat_tuples.add([(1, 2), (2,1), (1, 3), (3, 1) ... n
    # 2. Col: for all values in column i:
    # scope - var-cell(i,j), for i in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i+1,j)
    # iterate - add sat_tuples([(1,2) ...
    # put it all into a CSP

    pass

def cagey_csp_model(cagey_grid):
    # things to do: construct a binary constraint
    # All constraints:
    # 1. Row: for all values in a row i:
    # scope - var-cell(i,j), for j in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i, j+1)
    # itertools - sat_tuples.add([(1, 2), (2,1), (1, 3), (3, 1) ... n
    # 2. Col: for all values in column i:
    # scope - var-cell(i,j), for i in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i+1,j)
    # iterate - add sat_tuples([(1,2) ...
    # 3. NO - Kenken puzzle constraint:
    # scope - cage - cagey_grid([1][i]
    # operation on cells with operator == target ([0] of looped)
    # -> make helper fn for this
    # put it all into a CSP

    pass
