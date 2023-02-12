# =============================
# Student Names: Aarushi Mathur, Oscar Chen
# Group ID: 55
# Date: 5 February 2023
# =============================
# CISC 352 - W23
# propagators.py
# desc:
#


# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete problem solution.

""" This file will contain different constraint propagators to be used within
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instantiated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          propagator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constraints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   """


def prop_BT(csp, newVar=None):
    """Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints"""

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:  # no vars unassigned
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check_tuple(vals):  # if False, CSP constraint violated
                return False, []
    return True, []


def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    vals = []
    constraint = []
    tfvalue = 0

    if(newVar == None):
        constraint = csp.get_all_cons()
    else:
        constraint = csp.get_cons_with_var(newVar)

    for c in constraint:
        if c.get_n_unasgn() == 1:
            var = c.get_unasgn_vars()[0]

            for d in var.cur_domain():
                if not c.check_var_val(var, d):
                    pair = (var, d)
                    for i in vals:
                        if pair == i:
                            tfvalue += 1
                    if(tfvalue == 0):
                        vals.append(pair)
                        var.prune_value(d)

            if var.cur_domain_size() == 0:
                return False, vals

    return True, vals


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    tfvalue1 = 0
    tfvalue2 = 0
    vals = []
    queue = []

    if(newVar == None):
        constraints = csp.get_all_cons()
    else:
        constraints = csp.get_cons_with_var(newVar)

    for c in constraints:
        queue.append(c)

    while len(queue) != 0:
        c = queue.pop(0)
        for var in c.get_scope():
            for d in var.cur_domain():
                if not c.check_var_val(var, d):
                    pair = (var, d)
                    for i in vals:
                        if pair == i:
                            tfvalue1 += 1
                    if(tfvalue1 == 0):
                        vals.append(pair)
                        var.prune_value(d)
                    if var.cur_domain_size() == 0:
                        queue.clear()
                        return False, vals
                    else:
                        for cons in csp.get_cons_with_var(var):
                            for x in queue:
                                if (cons == x):
                                    tfvalue2 += 1
                            if (tfvalue2 == 0):
                                queue.append(cons)
    return True, vals
