# =============================
# Student Names: Aarushi Mathur, Oscan Chen
# Group ID: 55
# Date: 5 February 2023
# =============================
# CISC 352 - W23
# heuristics.py
# desc:
#


# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete problem solution.

"""This file will contain different constraint propagators to be used within
   the propagators

var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   """


def ord_dh(csp):
    """" return variables according to the Degree Heuristic """
    # make use of CSP method get_constr_with_var to check which var
    # has most constraints
    # we want to select only from unassigned vars
    # -> get_unassigned()
    # loop over unassigned -> get constraints
    # keep track of highest # of constraints
    # Runtime: O(n), n - no. of variables

    unassigned_vars = csp.get_all_unasgn_vars()
    # only want constraints on unassigned vars
    if len(unassigned_vars) == 0:
        return
        # no values remain unassigned. Nothing to be done.

    highest_degree_var = unassigned_vars[0]  # initially
    for variable in unassigned_vars:
        if len(csp.get_cons_with_var(variable)) > \
                len(csp.get_cons_with_var(highest_degree_var)):
            highest_degree_var = variable
    return highest_degree_var


def ord_mrv(csp):
    """ return variable according to the Minimum Remaining Values heuristic """

    # make use of method to get unassigned variables
    # var.curr_domain_size()
    # maintain track of which var is the min
    # return var with least remaining values to go first
    # Runtime O(n): <= n iterations of loops, where n <= total # of variables

    unassigned_vars = csp.get_all_unasgn_vars()
    if len(unassigned_vars) == 0:
        return
        # no values remain unassigned. Nothing to be done.

    min_remaining_vals = unassigned_vars[0]    # initially
    for variable in unassigned_vars:
        if variable.cur_domain_size() < min_remaining_vals.cur_domain_size():
            min_remaining_vals = variable
    return min_remaining_vals
