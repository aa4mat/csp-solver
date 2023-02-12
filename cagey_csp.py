# =============================
# Student Names: Aarushi Mathur, Oscan Chen
# Group ID: 55
# Date: 5 February 2023
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
    # val Var-Cell(i,j) != val Var-Cell(i, j+1), ...
    # itertools -> sat_tuples.add([(1, 2), (2,1), (1, 3), (3, 1) ... n
    # 2. Col: for all values in column j:
    # scope - var-cell(i,j), for i in 0 to n
    # val Var-Cell(i,j) != val Var-Cell(i+1,j)...
    # iterate - add sat_tuples([(1,2) ...
    # put it all into a CSP

    grid_size = cagey_grid[0]
    csp = CSP("Binary-ne-Cagey", [])    # initialise
    domain = [v for v in range(1, grid_size+1)]

    # initialise Variables, add to CSP
    variables = []
    for i in product(range(1, grid_size+1), repeat=2):
        new_var = Variable(("Cell" + str(i)), domain)
        variables.append(new_var)
        csp.add_var(new_var)

    # create scopes, create row constraint, add to CSP
    for row in range(1, grid_size+1):
        for i in permutations(range(1, grid_size+1), 2):
            # note - make this n for  all_diff?
            names = ["Cell(" + str(row) + ", " + str(i[0]) + ")",
                     "Cell(" + str(row) + ", " + str(i[1]) + ")"]
            scope_temp = []
            for var in variables:  # get Variable that matches name, to add to scope
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
            for var in variables:  # get Variable that matches name, to add to scope
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
    # scope - var-cell(row,j), for j in 0 to n
    # val Var-Cell(row,j) != val Var-Cell(row, j+1) for all j
    # itertools - sat_tuples.add([(1,2,3), (2,1,3), (1, 3,2), (3,1,2) ... n
    # 2. Col: for all values in column i:
    # scope - var-cell(i,col), for i in 0 to n
    # val Var-Cell(i,col) != val Var-Cell(i+1,j)
    # iterate - add sat_tuples([(1,2,3) ...
    # put it all into a CSP

    grid_size = cagey_grid[0]
    csp = CSP("nary-allDiff-Cagey", [])  # initialise
    domain = [v for v in range(1, grid_size + 1)]

    # initialise Variables, add to CSP
    variables = []
    for i in product(range(1, grid_size + 1), repeat=2):
        new_var = Variable(("Cell" + str(i)), domain)
        variables.append(new_var)
        csp.add_var(new_var)

    # create scopes, create row n-ary constraint, add to CSP
    for row in range(1, grid_size + 1):
        row_scope = list()
        for i in range(1, grid_size + 1):
            names = list()
            names.append("Cell({}, {})".format(row, i))
            scope_temp = []
            for var in variables:
                # get Variable that matches name, to add to scope
                # NOTE - creating a new variable won't work because matching
                # done by object, not by Variable name
                if var.name in names:
                    if not var in scope_temp:
                        scope_temp.append(var)  # n values

            row_scope.extend(scope_temp)
            # create constraint for each ROW

        cons = Constraint("N-ary-allDiff-Row({})".format(row), row_scope)

        sat_tuple = [tup for tup in permutations(range(1, grid_size + 1), grid_size)]
        cons.add_satisfying_tuples(sat_tuple)
        csp.add_constraint(cons)

    # create scopes, create column n-ary constraint, add to CSP
    for col in range(1, grid_size + 1):
        col_scope = list()
        for i in range(1, grid_size + 1):
            names = list()
            names.append("Cell({}, {})".format(i, col))
            scope_temp = []
            for var in variables:
                # get Variable that matches name, to add to scope
                # NOTE - creating a new variable won't work because matching
                # done by object, not by Variable name
                if var.name in names:
                    if var not in scope_temp:
                        scope_temp.append(var)  # n values

            col_scope.extend(scope_temp)
            # create constraint for each COLUMN

        cons = Constraint("N-ary-allDiff-Column({})".format(col), col_scope)

        sat_tuple = [tup for tup in
                     permutations(range(1, grid_size + 1), grid_size)]
        cons.add_satisfying_tuples(sat_tuple)
        csp.add_constraint(cons)

    return csp, []  # right now we don't care about the grid


def cagey_csp_model(cagey_grid):
    # things to do: construct a nary constraint
    # All constraints:
    # Row, col - nary
    # 3. Kenken puzzle constraint:
    # op([vars]) == target
    # scope - cage -> cagey_grid([1][i])
    # operation on cells with operator == target ([0] of looped)
    # -> make helper fn for this
    # put it all into a CSP

    # === n-ary constraint, copied from prev function ===

    grid_size = cagey_grid[0]
    csp = CSP("Full-Cagey", [])  # initialise
    domain = [v for v in range(1, grid_size + 1)]

    # initialise Variables, add to CSP
    variables = []
    for i in product(range(1, grid_size + 1), repeat=2):
        new_var = Variable(("Cell" + str(i)), domain)
        variables.append(new_var)
        csp.add_var(new_var)

    # create scopes, create row n-ary constraint, add to CSP
    for row in range(1, grid_size + 1):
        row_scope = list()
        for i in range(1, grid_size + 1):
            names = list()     # can be single str?
            names.append("Cell({}, {})".format(row, i))
            scope_temp = []
            for var in variables:
                # get Variable that matches name, to add to scope
                # NOTE - creating a new variable won't work because matching
                # done by object, not by Variable name
                if var.name in names:
                    if var not in scope_temp:
                        scope_temp.append(var)  # n values

            row_scope.extend(scope_temp)
            # create constraint for each ROW

        cons = Constraint("N-ary-allDiff-Row({})".format(row), row_scope)

        sat_tuple = [tup for tup in
                     permutations(range(1, grid_size + 1), grid_size)]
        cons.add_satisfying_tuples(sat_tuple)
        csp.add_constraint(cons)

    # create scopes, create column n-ary constraint, add to CSP
    for col in range(1, grid_size + 1):
        col_scope = list()
        for i in range(1, grid_size + 1):
            names = list()
            names.append("Cell({}, {})".format(i, col))
            scope_temp = []
            for var in variables:
                # get Variable that matches name, to add to scope
                # NOTE - creating a new variable won't work because matching
                # done by object, not by Variable name
                if var.name in names:
                    if var not in scope_temp:
                        scope_temp.append(var)  # n values

            col_scope.extend(scope_temp)
            # create constraint for each COLUMN

        cons = Constraint("N-ary-allDiff-Column({})".format(col), col_scope)

        sat_tuple = [tup for tup in
                     permutations(range(1, grid_size + 1), grid_size)]
        cons.add_satisfying_tuples(sat_tuple)
        csp.add_constraint(cons)

    # === cage constraints ===

    cages = cagey_grid[1]

    for cage in cages:
        target = cage[0]
        cage_vars = cage[1]      # list of cells
        cage_op = cage[2]        # get cage operator
        var_op_str = ""     # build string for naming cage operator variable
        cage_scope = list()
        # build cage constraint scope by looping over
        # all variables in the cage

        for i in range(len(cage_vars)):
            var_name = "Cell" + str(cage_vars[i])
            for var in variables:
                if var.name == var_name:
                    if var not in cage_scope:
                        # just in case; should be unique already
                        cage_scope.append(var)
                        var_op_str += "Var-Cell({},{}), "\
                            .format(cage_vars[i][0], cage_vars[i][1])
        # all cell vars added. Add operator var to scope
        var_name_string = "Cage_op({}:{}:[{}])".format(target, cage_op, var_op_str[0:-2])
        # -2: strip final ', '
        op_var = Variable(var_name_string, ['+', '-', '/', '*', '?'])
        variables.append(op_var)
        csp.add_var(op_var)
        cage_scope.insert(0, op_var)
        # Keeping var order same as Constraint name in spec
        cons = Constraint(var_name_string, cage_scope)
        # since cons name doesn't matter, just naming it the same as the var

        # get satisfying tuples for constraint by evaluating:
        sat_tuples = eval_sat_tuples((len(cage_scope)-1), cage_op, target, grid_size)
        cons.add_satisfying_tuples(sat_tuples)
        csp.add_constraint(cons)

    return csp, variables


def eval_sat_tuples(n, operator, target, grid_size) -> list:
    """An aggregator function to evaluate the constraint,
    returns a list of satisfying tuples [sat_tuples]
    """
    sat_tuples = list()
    # n => no. of cell vars (excluding cage_op)
    if n == 1:  # just 1 var, won't waste computation checking
        return [(operator, target)]
    # note: if '?' causes problems, fix '+' as default.

    for tup in product(range(1, grid_size + 1), repeat=n):
        if (operator == '+') or (operator == '?'):
            if sum(tup) == target:  # satisfies!
                sat = ('+',) + tup
                sat_tuples.append(sat)
        if operator == '*' or (operator == '?'):
            aggr = tup[0]  # manually multiplying bc my python version is 3.7 :(
            for i in range(1, len(tup)):
                aggr *= tup[i]
            if aggr == target:
                sat = ('*',) + tup
                sat_tuples.append(sat)
        if operator == '-' or (operator == '?'):
            aggr = tup[0]
            for i in range(1, len(tup)):
                aggr -= tup[i]
            if aggr == target:
                # add all permutations of this to sat_tuples:
                # i.e. (1, 2, 3), (1, 3, 2)... all satisfy constraint
                p_list = [p for p in permutations(tup, n)]
                sat = []
                for p in p_list:
                    sat.append(('-', ) + p)  # include operator
                sat_tuples.extend(sat)
        if operator == '/' or (operator == '?'):
            aggr = tup[0]
            for i in range(1, len(tup)):
                aggr = int(aggr / tup[i])   # no fractions
            if aggr == target:
                # add all permutations of this to sat_tuples
                p_list = [p for p in permutations(tup, n)]
                sat = []
                for p in p_list:
                    sat.append(('/',) + p)  # include operator
                sat_tuples.extend(sat)

    return sat_tuples
