from z3 import substitute, is_true, sat, unsat, simplify, Bool, BitVec, BoolVector, BoolVal, Not, If, And, Or, Exists, ForAll, Implies, Solver, Optimize, to_symbol, Sum, Distinct

import itertools
from tqdm import tqdm
import numpy as np
import matplotlib.pyplot as plt
import time
import re
import os
from pandas import read_csv
import fcntl
from multiprocessing import Pool
from functools import partial

import random

from collections import defaultdict

# Applies selected reaction logic to BooleanVector species variables
# EX:  ren = Bool('r_en')
#      spe = BoolVector('spe', 4)
#      react(ren,  spe, [0, 1], [2, 3])
#      print(spe)
def react(rbool, species, s_ins, s_outs):
    r_out = And(rbool, *[species[s] for s in s_ins])
    for s_out in s_outs:
        species[s_out] = Or(r_out, species[s_out])

def SMT_expr_equiv(old, new):
    slvr = Solver()
    slvr.add(Not(old == new))
    return slvr.check() == unsat

# Applies selected reaction logic to BooleanVector species variables. 
# Uses simplify, and uses z3 to check if the new update application is necessary
# EX:  ren = Bool('r_en')
#      spe = BoolVector('spe', 4)
#      react(ren,  spe, [0, 1], [2, 3])
#      print(spe)
# THIS IS INCOMPATIBLE WITH RIEDEL!! ... ITS BECAUSE ONCE AN OUTPUT SPECIES IS TURNED ON IT CANT TURN BACK OFF ... GO THROUGH THE 010 CASE OF THE RIEDEL EXAMPLE I HAVE
def react_and_check(rbool, species, s_ins, s_outs):
    updates = False
    r_out = And(rbool, *[species[s] for s in s_ins])
    for s_out in s_outs:
        new_species = simplify(Or(r_out, species[s_out]))
        # If the new species is different from the old one, update it
        if not SMT_expr_equiv(new_species, species[s_out]):
            updates = True
            species[s_out] = new_species
    return updates

def react_and_check_(rbool, species, s_ins, s_outs):
    updates = False
    species_after = species.copy()
    react(rbool, species_after, s_ins, s_outs)
    # use SMT_expr_equiv, only update species if the new expression is different from the old one
    for s_out in s_outs:
        if not SMT_expr_equiv(species[s_out], species_after[s_out]):
            updates = True
            species[s_out] = species_after[s_out]
    return updates


    # r_out = And(rbool, *[species[s] for s in s_ins])
    # for s_out in s_outs:
    #     new_species = simplify(Or(r_out, species[s_out]))
    #     # species[s_out] = new_species
    #     # If the new species is different from the old one, update it
    #     slvr = Solver()
    #     slvr.add(Not(new_species == species[s_out]))
    #     if slvr.check() == sat:
    #         updates = True
    #         species[s_out] = new_species
    # return updates

# s_ins_and_incoming_reactions is a list reactants as tuples, where the first element of the tuple is the species index, and the second element is the list of reactions that produce that species
# assume that output of gates already initialized with correct variables
def react_and_check_GATES_OR_INS(species, reactions, reacts, out_species, riedel=True):

    # all of the reactions, grouped by products
    reactions_by_products = defaultdict(list)
    for i, (reactants, products) in enumerate(reactions):
        for p in products:
            reactions_by_products[p].append(i)


    if riedel:
        gate_initial_vals = BoolVector('gate_initial', len(reactions))
    else:
        gate_initial_vals = [False for _ in reactions]
    # forall_vars will be subset of gate_initial_vals  -- one for each gate, none for wires
    forall_vars = set()
    
    # this tries to 'bubble' as many times as possible
    for time_index, _ in enumerate(reactions):
        first_run = time_index == 0
        # this bubbles inputs to outputs 1 time for each gate
        for gate_i, (reactants, products) in enumerate(reactions):
            # this strategy skips wires completely - the gates will compute wires incoming to them
            
            if len(reactants) == 1:
                continue
            
            s_ins = [species[gate_in] for gate_in in reactants]

            # now go through each input and or all wire values (including wire enables) that come into it
            for i, gate_in in enumerate(reactants):
                incoming_reactions = reactions_by_products[gate_in]
                for wire_i in incoming_reactions:
                    w_ins, w_outs = reactions[wire_i]
                    assert len(w_ins) == 1 and len(w_outs) == 1
                    if first_run:
                        from_gate = reactions_by_products[w_ins[0]]
                        assert len(from_gate) == 1
                        wire_val = gate_initial_vals[from_gate[0]]
                        if riedel:
                            forall_vars.add(wire_val)
                    else:
                        wire_val  = species[w_ins[0]]
                    wire_en = reacts[wire_i]

                    s_ins[i] = simplify(Or(s_ins[i], And(wire_en, wire_val)))

            # now s_in is a list of expressions that are the inputs to the gate
            gate_en = reacts[gate_i]
            new_gate_out = simplify(And(gate_en, *s_ins))
            
            # now check if the new gate output is different from the old one
            slvr = Solver()
            slvr.add(Not(new_gate_out == species[products[0]]))
            if slvr.check() == sat:
                # set all gate products to the new gate output
                for gate_out in products:
                    species[gate_out] = new_gate_out

    # now bubble wires for outputs.
    for out_i in out_species:
        incoming_reactions = reactions_by_products[out_i]
        wi_i_sout = [wire_i for wire_i in incoming_reactions]
        # make sure its only wires going to outputs.
        assert all([len(reactions[w_i][0]) == 1 and len(reactions[w_i][1]) == 1 for w_i in wi_i_sout])
        # or all the wires together, with their enables
        # print()
        species[out_i] = simplify(Or(*[And(reacts[w_i], species[reactions[w_i][0][0]]) for w_i in wi_i_sout]))
        # value_from = reactions[incoming_reactions[0]][0][0]
        # species[out_i] = And(reacts() species[value_from]

    return list(forall_vars)

# Translates z3 Boolean expression to concrete True or False
# EX:  print( f_z3_concrete( Or(False, False, True) ) )
def f_z3_concrete(z3_exp):
    return is_true(simplify(z3_exp))


def getElement(l, i):
    out = l[len(l)-1]
    for index in range(len(l)-2, -1, -1):
        out = If(i == index, l[index], out)
    return out

def count(xs, ref, occurs=True):
    s = 0
    for x in xs:
        s += If(x == ref, 1 if occurs else 0, 0 if occurs else 1)
    return s

def only_one_enabled(vals):
    expr = []
    for i in range(len(vals)):
        for j in range(i):
            expr.append(Implies(vals[i], Not(vals[j])))
    return simplify(And(*expr))

def only_one_enabled2(vals):
    expr = []
    for i in range(len(vals)):
        expr.append(And(vals[i], Not(Or(vals[:i] + vals[i+1:]))))
    return simplify(Or(*expr))

def most_one_enabled2(vals):
    expr = []
    for i in range(len(vals)):
        expr.append(And(vals[i], Not(Or(vals[:i] + vals[i+1:]))))
    return simplify(Or(*expr, And(*[Not(v) for v in vals])))
#    return Or([And(*[r == r_i for r_i in rs]) for r in rs])

def most_one_enabled3(vals):
    return (count(vals, True, occurs=True) <= 1)


def distinct_except(l, vals):
    expr = []
    for i in range(len(l)):
        for j in range(i):
            #vals.append(Implies(And(l[i] > val, l[j] > val), l[i] != l[j]  ))
            expr.append(Implies(And(*[And(l[i] != val, l[j] != val) for val in vals]), l[i] != l[j] ))
            #expr.append(Implies(And(l[i] != 0, l[i] != 1, l[j] != 0, l[j] != 1), l[i] != l[j]  ))
    return simplify(And(*expr))


def allowed_values(x, allowed):
    return Or([x == a for a in allowed])

def evalf3(fnum, xs):
    assert len(xs) == 3, ''
    func = Or(    
        And(bool(fnum & (1 << 0)), Not(xs[2]), Not(xs[1]), Not(xs[0])),
        And(bool(fnum & (1 << 1)), Not(xs[2]), Not(xs[1]),     xs[0] ),
        And(bool(fnum & (1 << 2)), Not(xs[2]),     xs[1] , Not(xs[0])),
        And(bool(fnum & (1 << 3)), Not(xs[2]),     xs[1] ,     xs[0] ),
        And(bool(fnum & (1 << 4)),     xs[2] , Not(xs[1]), Not(xs[0])),
        And(bool(fnum & (1 << 5)),     xs[2] , Not(xs[1]),     xs[0] ),
        And(bool(fnum & (1 << 6)),     xs[2] ,     xs[1] , Not(xs[0])),
        And(bool(fnum & (1 << 7)),     xs[2] ,     xs[1] ,     xs[0] ))
    return simplify(func)

def evalf4(fnum, xs):
    assert len(xs) == 4, ''
    func = Or(    
        And(bool(fnum & (1 << 0)), Not(xs[3]), Not(xs[2]), Not(xs[1]), Not(xs[0])),
        And(bool(fnum & (1 << 1)), Not(xs[3]), Not(xs[2]), Not(xs[1]),     xs[0] ),
        And(bool(fnum & (1 << 2)), Not(xs[3]), Not(xs[2]),     xs[1] , Not(xs[0])),
        And(bool(fnum & (1 << 3)), Not(xs[3]), Not(xs[2]),     xs[1] ,     xs[0] ),
        And(bool(fnum & (1 << 4)), Not(xs[3]),     xs[2] , Not(xs[1]), Not(xs[0])),
        And(bool(fnum & (1 << 5)), Not(xs[3]),     xs[2] , Not(xs[1]),     xs[0] ),
        And(bool(fnum & (1 << 6)), Not(xs[3]),     xs[2] ,     xs[1] , Not(xs[0])),
        And(bool(fnum & (1 << 7)), Not(xs[3]),     xs[2] ,     xs[1] ,     xs[0] ),

        And(bool(fnum & (1 << 8)),     xs[3] , Not(xs[2]), Not(xs[1]), Not(xs[0])),
        And(bool(fnum & (1 << 9)),     xs[3] , Not(xs[2]), Not(xs[1]),     xs[0] ),
        And(bool(fnum & (1 << 10)),    xs[3] , Not(xs[2]),     xs[1] , Not(xs[0])),
        And(bool(fnum & (1 << 11)),    xs[3] , Not(xs[2]),     xs[1] ,     xs[0] ),
        And(bool(fnum & (1 << 12)),    xs[3] ,     xs[2] , Not(xs[1]), Not(xs[0])),
        And(bool(fnum & (1 << 13)),    xs[3] ,     xs[2] , Not(xs[1]),     xs[0] ),
        And(bool(fnum & (1 << 14)),    xs[3] ,     xs[2] ,     xs[1] , Not(xs[0])),
        And(bool(fnum & (1 << 15)),    xs[3] ,     xs[2] ,     xs[1] ,     xs[0] ))
    return simplify(func)


def phi_func_i(f_num, x_ins):
    if f_num == 0:
        return BoolVal(False)
    if len(x_ins) == 3:
        return evalf3(f_num, x_ins)
    elif len(x_ins) == 4:
        return evalf4(f_num, x_ins)
    else:
        assert False

def bits_select(l):
    return max(1, (len(l)-1).bit_length())

#force_f2o=[0,1] only if get_inv_4G_complete_cyclic() is used
# force_f2o is TEMP! it should be =None
def setup(reactions, in_species, out_species, N_XVARS, N_FUNCS, inputs_distinct=True, riedel=False, force_f2o=None): # =None): #=[0,1]):   # =None):
    assert len(out_species) >= N_FUNCS, 'Not enough output species to encode all functions'

    # Sets up specified fridge and function, in Z3 expressions
    N_REACTIONS = len(reactions)

    reacts = BoolVector('r', N_REACTIONS)
    x_vars = BoolVector('x', N_XVARS)
    x_ins  = [False, True] + [ Not(x_vars[i//2]) if i%2 == 0 else x_vars[i//2] for i in range(N_XVARS*2)]
    # [False, True, Not(x__0), x__0, Not(x__1), x__1, Not(x__2), x__2, ...]


    N_SPECIES = max([max(*r,*p) for r,p in reactions])+1



    # all of the reactions, grouped by reactants
    # print(list(enumerate(reactions)))

    reacts_by_reactants = defaultdict(list) 
    for i, (reactants, products) in enumerate(reactions):
        for r in reactants:
            reacts_by_reactants[r].append(i)
    #reacts_by_reactants = { reactant:react_is for (reactant,react_is) in reacts_by_reactants.items() if len(react_is) > 1 }
    reacts_by_reactants_more1 = { reactant:react_is for (reactant,react_is) in reacts_by_reactants.items() if len(react_is) > 1 }

    i2x_list = [BitVec('i2x__' + str(i), bits_select(x_ins)) for i in in_species]


    gates = [react_var for (react_var, react) in zip(reacts, reactions) if (len(react[0]) > 1 or len(react[1]) > 1) ]
    wires = [react_var for (react_var, react) in zip(reacts, reactions) if (len(react[0]) == 1 and len(react[1]) == 1) ]
    n_gates = simplify(count(gates, True))
    n_wires = simplify(count(wires, True))
    n_fuel_inputs = simplify(count(i2x_list, 1))
    n_inputs = simplify(count(i2x_list, 0, occurs=False))


    cost_gates_wires_inputs = simplify(n_gates + n_wires + n_inputs)
    cost_gates_wires_trues = simplify(n_gates + n_wires + n_fuel_inputs)
    cost = cost_gates_wires_trues

    cost_minimize = [n_gates, n_wires, n_fuel_inputs]


    # force_f2o = [0,1]
    if force_f2o is None:
        f2o_list = [BitVec('f2o__' + str(f), bits_select(out_species)) for f in range(N_FUNCS)]
    else:
        f2o_list = force_f2o

    species_initial = [False] * N_SPECIES
   # We also need to "Or" that value with whatever getElement(x_ins, i2x) returns to get the initial value of species
    for i, i2x in zip(in_species, i2x_list):
        # species_initial[i] = Bool('SIN_init' + str(i)) 
        species_initial[i] = simplify(getElement(x_ins, i2x))


    # print('mm')
    species = [si for si in species_initial]

    # start timer
    start = time.time()

    # react_and_check(r_enable, species, r_reactants, r_products)

    # Inner loop calls react() for each specified reaction
    # Outer loop repeats this for number of reactions, to bubble logic all the way to products 
    #  * Outer is necessary if reactions are specified out of order, or if there is no clear order (cyclic)
    # react_and_check() doesn't let the terms accumulate unnessarily (uses z3 to not accumulate unnecessarily).
    # react_and_check returns True if any species were updated

    if riedel:
        forall_vars = react_and_check_GATES_OR_INS(species, reactions, reacts, out_species)
    else:
        forall_vars = []
        for i in range(N_REACTIONS):
            still_updating = False
            for r_enable, (r_reactants, r_products) in zip(reacts, reactions):
                still_updating |= react_and_check(r_enable, species, r_reactants, r_products)
            if not still_updating:
                break

    end = time.time()

    # print('forall_vars', forall_vars)
    # print('species', species)
    # print('species... ', list(enumerate(species)))



    # print('Time to react: ' + str(end - start))
    # with open('cyc5.smt2', 'w') as text_file:
    #     print([s.sexpr() for s in species], file=text_file)


    # Select logical output, and simplify symbolic equation for efficiency (# MIGHT INSTEAD DO THIS EVERY TIME WE CALL REACT)
    #out_s = simplify(getElement(species, getElement(out_species, i2o)))

    if force_f2o is None:
        outs_f = [simplify(getElement(species, getElement(out_species, f2o))) for f2o in f2o_list]
    else:
        outs_f = [simplify(getElement(species, out_species[f2o])) for f2o in f2o_list]

    # print(outs_f)

    constraint_i2x = simplify(And([allowed_values(i2x, range(len(x_ins))) for i2x in i2x_list]))

    if force_f2o is None:
        constraint_f2o = simplify(And([allowed_values(f2o, range(len(out_species))) for f2o in f2o_list]))
        # requires that all f2o are distinct
        constraint_f2o_distinct = distinct_except(f2o_list, [])
    else:
        constraint_f2o = True
        constraint_f2o_distinct = True
    
    #constraint_i2o = allowed_values(i2o, range(len(out_species)))

    constraint_inputs_distinct = distinct_except(i2x_list, [0,1])

    # reacts_en = [(r, True if (i in [ii for ii,rr in reactions_en]) else False)  for i, r in enumerate(reacts)]
    # print(reacts_en)
    # print('\noh!\n\n', concretize(constraint_outputs_distinct, [r[0] for r in reacts_en], [r[1] for r in reacts_en]))


    # outputs of gates and wires can't be fanned out to multiple inputs
    #constraint_outputs_distinct = only_one_enabled([And(reacts[i], species[reactants[0]]) for i, (reactants, products) in enumerate(reactions) if len(reactants) == 1 and len(products) == 1
    

    # outputs of gates and wires can't be fanned out to multiple inputs
    constraint_outputs_distinct = simplify(And([most_one_enabled2([reacts[i] for i in react_is]) for reactant, react_is in reacts_by_reactants_more1.items()]))
    #print('constraint_outputs_distinct', constraint_outputs_distinct)

    if inputs_distinct:
        constraints = simplify(And(constraint_i2x, constraint_f2o, constraint_f2o_distinct, constraint_outputs_distinct, constraint_inputs_distinct))
    else:
        constraints = simplify(And(constraint_i2x, constraint_f2o, constraint_f2o_distinct, constraint_outputs_distinct))

    model_vars = (x_ins, i2x_list, f2o_list, reacts, species)
    return (x_vars, outs_f, constraints, cost, cost_minimize, model_vars, forall_vars)


def meval(model, expr):
    if model is None or expr is None:
        return None
    elif hasattr(expr, '__iter__'):
        return [model.eval(e, model_completion=True) for e in expr]
    else:
        return model.eval(expr, model_completion=True)

def meval_long(model, expr):
    if model == None:
        return float('nan')
    if expr == None:
        return 0
    
    out = meval(model, expr)
    if out == None:
        return float('nan')
    else:
        return out.as_long()



def open_resume(filename):
    last_line = "0"
    if os.path.exists(filename):
        with open(filename) as f:
            for line in f:
                last_line = line
    
    last_f_i = int(re.search(r'\d+', last_line).group())

    if last_f_i == 0:
        f = open(filename, "w")
    else:
        f = open(filename, "a")
        last_f_i += 1

    return (f, last_f_i)


def get_inv_19g_27w():
    # Possible reactions in your fridge (tuple of reactant ID's, tuple of product ID's)
    inv_name = '19G 27W Inventory'

    reactions = [
        [(0,   1), (20, 21)], #0
        [(2,   3), (22, 23)], #1
        [(4,   5), (24, 25)], #2
        [(6,   7), (26, 27)], #3
        [(8,   9), (28, 29)], #4
        [(10, 11), (30, 31)], #5
        [(12, 13), (32, 33)], #6
        [(14, 15), (34, 35)], #7
        [(16, 17), (36, 37)], #8
        [(18, 19), (38, 39)], #9

        [(40, 41), (58, 59)], #10
        [(42, 43), (60, 61)], #12
        [(44, 45), (62, 63)], #13
        [(46, 47), (64, 65)], #14
        [(48, 49), (66, 67)], #15
        [(50, 51), (68, 69)], #16
        [(52, 53), (70, 71)], #17
        [(54, 55), (72, 73)], #18
        [(56, 57), (74, 75)], #19


        [(20,), (40,)], #0
        [(21,), (42,)], #1
        [(22,), (41,)], #2
        [(23,), (44,)], #3
        [(24,), (43,)], #4
        [(25,), (46,)], #5
        [(26,), (45,)], #6
        [(27,), (47,)], #7
        [(28,), (48,)], #8
        [(29,), (50,)], #9
        [(30,), (49,)], #10
        [(31,), (52,)], #11
        [(32,), (51,)], #12
        [(33,), (54,)], #13
        [(34,), (53,)], #14
        [(35,), (55,)], #15
        [(36,), (56,)], #16
        [(38,), (57,)], #17

        [(58,), (76,)], #18
        [(60,), (76,)], #19
        [(62,), (76,)], #20
        [(64,), (76,)], #21
        [(66,), (76,)], #22
        [(68,), (76,)], #23
        [(70,), (76,)], #24
        [(72,), (76,)], #25
        [(74,), (76,)], #26
    ]

    # options for species that could be assigned a logic input 
    in_options = list(range(0,20)) + list(range(40,58))

    # Maps logic output to species ID
    out_species = [76]
    inputs_distinct = False

    return (inv_name, reactions, in_options, out_species, inputs_distinct)

def get_inv_19g_27w_in_distint():
    (inv_name, reactions, in_options, out_species, inputs_distinct) = get_inv_19g_27w()
    inputs_distinct = True
    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_1g_1w():
    inv_name = '1G tiny Acyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0

        [(2,), (4,)], #1

    ]
    in_options = [0, 1]

    out_species = [4]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_2g_small_acyclic():
    inv_name = '2G Small Acyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1

        [(3,), (5,)], #0
        [(2,), (8,)], #1
        [(7,), (9,)], #2 

        # [(3,), (4,)], #3 
        [(2,), (4,)], #3 
        [(3,), (9,)], #4

        # CYCLE!!!
        # [(6,), (0,)], #4
        # [(6,), (1,)], #5
    ]
    in_options = [0, 1, 4, 5]

    out_species = [8, 9]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)

def get_inv_2g_small_cyclic():
    inv_name = '2G Small Cyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1

        [(3,), (5,)], #2
        [(2,), (8,)], #3
        [(7,), (9,)], #4 

        # [(3,), (4,)], #5 
        [(2,), (4,)], #5



        # CYCLE!!!
        [(6,), (0,)], #6
        [(6,), (1,)], #7
        [(2,), (5,)], #8
    ]
    in_options = [0, 1, 4, 5]

    out_species = [8, 9]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_2g_4w_cyclic():
    inv_name = '2G 4W custm Cyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1

        [(2,), (4,)], #2
        [(6,), (0,)], #3

        [(3,), (8,)], #4
        [(7,), (9,)], #5
    ]
    in_options = [0, 1, 4, 5]

    out_species = [8, 9]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_4G_complete_acyclic():
    inv_name = '4G Complete Acyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3

        # reporters
        [(2,), (16,)],
        [(6,), (17,)],
        [(10,), (18,)],
        [(14,), (19,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)] for i in [4, 5, 8, 9, 12, 13]] + \
        [[(3,), (i,)] for i in [4, 5, 8, 9, 12, 13]] + \
        [[(6,), (i,)] for i in [8, 9, 12, 13]] + \
        [[(7,), (i,)] for i in [8, 9, 12, 13]] + \
        [[(10,), (i,)] for i in [12, 13]] + \
        [[(11,), (i,)] for i in [12, 13]] #+ \
        # [[(14,), (i,)] for i in [0, 1, 4, 5, 8, 9]] + \
        # [[(15,), (i,)] for i in [0, 1, 4, 5, 8, 9]]


    in_options = [0,1,4,5,8,9,12,13]

    out_species = [16, 17, 18, 19]
    #out_species = [2, 3, 6, 7, 10, 11, 14, 15]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_4G_custom_cyclic():
    inv_name = '4G Custom Cyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3

        # reporters
        [(2,), (16,)],
        [(6,), (17,)],
        [(10,), (18,)],
        [(14,), (19,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)] for i in [4, 5, 8, 9, 12, 13]] + \
        [[(3,), (i,)] for i in [4, 5, 8, 9, 12, 13]] + \
        [[(6,), (i,)] for i in [8, 9, 12, 13]] + \
        [[(7,), (i,)] for i in [8, 9, 12, 13]] + \
        [[(10,), (i,)] for i in [12, 13]] + \
        [[(11,), (i,)] for i in [12, 13]] #+ \
        # [[(14,), (i,)] for i in [0, 1, 4, 5, 8, 9]] + \
        # [[(15,), (i,)] for i in [0, 1, 4, 5, 8, 9]]

    cycle_reactions = \
        [[(6,), (i,)] for i in [0, 1]] + \
        [[(7,), (i,)] for i in [0, 1]] + \
        [[(10,), (i,)] for i in [0, 1, 4, 5]] + \
        [[(11,), (i,)] for i in [0, 1, 4, 5]] + \
        [[(14,), (i,)] for i in [0, 1, 4, 5, 8, 9]] + \
        [[(15,), (i,)] for i in [0, 1, 4, 5, 8, 9]]
    
    # pick 12 random reactions of the cycle reactions
    random.seed(0)
    cycle_reactions_50 = random.sample(cycle_reactions, len(cycle_reactions)//2)
    reactions += cycle_reactions_50

    
    in_options = [0,1,4,5,8,9,12,13]

    out_species = [16, 17, 18, 19]
    #out_species = [2, 3, 6, 7, 10, 11, 14, 15]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_3G_complete_acyclic():
    inv_name = '4G Complete Acyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        # [(12,13), (14,15)], #3

        # reporters
        [(2,), (12,)],
        [(6,), (13,)],
        [(10,), (14,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)] for i in [4, 5, 8, 9]] + \
        [[(3,), (i,)] for i in [4, 5, 8, 9]] + \
        [[(6,), (i,)] for i in [8, 9]] + \
        [[(7,), (i,)] for i in [8, 9]]

    in_options = [0,1,4,5,8,9]

    out_species = [12, 13, 14]
    #out_species = [2, 3, 6, 7, 10, 11, 14, 15]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_3G_complete_cyclic():
    inv_name = '3G Complete Cyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        # [(12,13), (14,15)], #3

        # reporters
        [(2,), (12,)],
        [(6,), (13,)],
        # [(10,), (14,)],
        # [(14,), (19,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)] for i in [4, 5, 8, 9]] + \
        [[(3,), (i,)] for i in [4, 5, 8, 9]] + \
        [[(6,), (i,)] for i in [0, 1, 8, 9]] + \
        [[(7,), (i,)] for i in [0, 1, 8, 9]] + \
        [[(10,), (i,)] for i in [0, 1, 4, 5]] + \
        [[(11,), (i,)] for i in [0, 1, 4, 5]]

    in_options = [0,1,4,5,8,9]

    #out_species = [2, 6, 10, 14]
    #out_species = [16, 17, 18, 19]
    out_species = [12, 13]

    # I force these 2 as outputs for the 2F test! See "force_f2o=[0,1]"

    #out_species = [2, 3, 6, 7, 10, 11, 14, 15]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)
# print(get_inv_4G_complete_cyclic()[1])



def get_inv_4G_complete_cyclic():
    inv_name = '4G Complete Cyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3

        # reporters
        [(2,), (16,)],
        [(6,), (17,)],
        # [(10,), (18,)],
        # [(14,), (19,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)] for i in [4, 5, 8, 9, 12, 13]] + \
        [[(3,), (i,)] for i in [4, 5, 8, 9, 12, 13]] + \
        [[(6,), (i,)] for i in [0, 1, 8, 9, 12, 13]] + \
        [[(7,), (i,)] for i in [0, 1, 8, 9, 12, 13]] + \
        [[(10,), (i,)] for i in [0, 1, 4, 5, 12, 13]] + \
        [[(11,), (i,)] for i in [0, 1, 4, 5, 12, 13]] + \
        [[(14,), (i,)] for i in [0, 1, 4, 5, 8, 9]] + \
        [[(15,), (i,)] for i in [0, 1, 4, 5, 8, 9]]

    in_options = [0,1,4,5,8,9,12,13]

    #out_species = [2, 6, 10, 14]
    #out_species = [16, 17, 18, 19]
    out_species = [16, 17]

    # I force these 2 as outputs for the 2F test! See "force_f2o=[0,1]"

    #out_species = [2, 3, 6, 7, 10, 11, 14, 15]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)
# print(get_inv_4G_complete_cyclic()[1])



def get_inv_5G_complete_acyclic():
    inv_name = '5G Complete Acyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3
        [(16,17), (18,19)], #4

        # reporters
        [(2,), (20,)],
        [(6,), (21,)],
        [(10,), (22,)],
        [(14,), (23,)],
        [(18,), (24,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)]  for i in [4, 5, 8, 9, 12, 13, 16, 17]] + \
        [[(3,), (i,)]  for i in [4, 5, 8, 9, 12, 13, 16, 17]] + \
        [[(6,), (i,)]  for i in [8, 9, 12, 13, 16, 17]] + \
        [[(7,), (i,)]  for i in [8, 9, 12, 13, 16, 17]] + \
        [[(10,), (i,)] for i in [12, 13, 16, 17]] + \
        [[(11,), (i,)] for i in [12, 13, 16, 17]] + \
        [[(14,), (i,)] for i in [16, 17]] + \
        [[(15,), (i,)] for i in [16, 17]] #+ \
        # [[(14,), (i,)] for i in [0, 1, 4, 5, 8, 9]] + \
        # [[(15,), (i,)] for i in [0, 1, 4, 5, 8, 9]]

    in_options = [0,1,4,5,8,9,12,13,16,17]

    out_species = [20, 21, 22, 23, 24]
    
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_5G_complete_cyclic():
    inv_name = '5G Complete Cyclic Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3
        [(16,17), (18,19)], #4

        # reporters
        [(2,), (20,)],
        [(6,), (21,)],
        [(10,), (22,)],
        [(14,), (23,)],
        [(18,), (24,)],
    ]

    # 48 internal wires! 6 wires from each output
    reactions += \
        [[(2,), (i,)]  for i in [4, 5, 8, 9, 12, 13, 16, 17]] + \
        [[(3,), (i,)]  for i in [4, 5, 8, 9, 12, 13, 16, 17]] + \
        [[(6,), (i,)]  for i in [0, 1, 8, 9, 12, 13, 16, 17]] + \
        [[(7,), (i,)]  for i in [0, 1, 8, 9, 12, 13, 16, 17]] + \
        [[(10,), (i,)] for i in [0, 1, 4, 5, 12, 13, 16, 17]] + \
        [[(11,), (i,)] for i in [0, 1, 4, 5, 12, 13, 16, 17]] + \
        [[(14,), (i,)] for i in [0, 1, 4, 5,  8,  9, 16, 17]] + \
        [[(15,), (i,)] for i in [0, 1, 4, 5,  8,  9, 16, 17]] + \
        [[(18,), (i,)] for i in [0, 1, 4, 5,  8,  9, 12, 13]] + \
        [[(19,), (i,)] for i in [0, 1, 4, 5,  8,  9, 12, 13]]

    in_options = [0,1,4,5,8,9,12,13,16,17]
    # in_options = [0,1,4,5,8,9,12,13]

    #out_species = [2, 6, 10, 14]
    #out_species = [16, 17, 18, 19]

    # I force these 2 as outputs for the 2F test! See "force_f2o=[0,1]"
    out_species = [20, 21]

    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)
# print(get_inv_4G_complete_cyclic()[1])


def get_inv_5g_12w():
    inv_name = '5G 12W Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3
        [(16,17), (18,19)], #4

        [(2,), (20,)], #5

        [(6,), (21,)], #6
        [(7,), (20,)], #7

        [(10,), (1,)], #8
        [(10,), (21,)], #9
        [(11,), (4,)], #10
        [(11,), (5,)], #11

        [(14,), (1,)], #12
        [(14,), (5,)], #13
        [(15,), (4,)], #14
        [(15,), (21,)], #15

        [(18,), (0,)], #16
    ]
    in_options = [0,1,4,5,8,9,12,13,16,17]

    out_species = [20, 21]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def get_inv_5g_13w_cyc():
    inv_name = '5G 13W cyc Inventory'
    reactions = [
        [(0, 1),  (2, 3)], #0
        [(4, 5),  (6, 7)], #1
        [(8, 9),  (10,11)], #2
        [(12,13), (14,15)], #3
        [(16,17), (18,19)], #4

        [(2,), (20,)], #5

        [(6,), (21,)], #6
        [(7,), (20,)], #7

        [(10,), (1,)], #8
        [(10,), (21,)], #9
        [(11,), (4,)], #10
        [(11,), (5,)], #11

        [(14,), (1,)], #12
        [(14,), (5,)], #13
        [(15,), (4,)], #14
        [(15,), (21,)], #15

        [(18,), (0,)], #16


        [(3,), (12,)], #17
    ]
    in_options = [0,1,4,5,8,9,12,13,16,17]

    out_species = [20, 21]
    inputs_distinct = True

    return (inv_name, reactions, in_options, out_species, inputs_distinct)


def trickle_circuit(species_vals, reactions_en, out_maps):
    prev_species = {}
    for _ in range(len(reactions_en) + 1):
        prev_species = species_vals.copy()
        for (i, (r_reactants, r_products)) in reactions_en:
            and_in = all([species_vals[r] for r in r_reactants])
            for p in r_products:
                species_vals[p] |= and_in

    assert species_vals == prev_species, "The species were still changing! \nspecies:\n{}\n\nprev_species:\n{}\n".format(species_vals, prev_species)

    out = [False if f_out not in species_vals else species_vals[f_out] for f_out in out_maps]
    return out




def evaluate_circuit(circuit, x_vars_concrete, riedel=False):
    x_ins_concrete = [False, True] + [ not x_vars_concrete[i//2] if i%2 == 0 else x_vars_concrete[i//2] for i in range(len(x_vars_concrete)*2)]

    (reactions_en, in_maps, out_maps) = circuit

    #print(circuit)
    #species 
    species_vals = {}
    products = set()
    for (i, (r_reactants, r_products)) in reactions_en:
        # print(i, r_reactants, r_products)
        products.update(r_products)
        for num in r_reactants + r_products:
            # print(" - ", num)
            species_vals[num] = False
    
    # print("products: ", products)
    # print("species_vals: ", species_vals)

    products = list(products)
    if riedel:
        out = None
        prev_prod_assign = None
        for i, species_assignment in enumerate(itertools.product((False, True), repeat=len(products))):
            species_vals_t = species_vals.copy()
            prod_assign = list(zip(products, species_assignment))
            for (product, assigned) in prod_assign:
                species_vals_t[product] = assigned

            for (specie, x_in) in in_maps:
                species_vals_t[specie] |= x_ins_concrete[x_in]


            out_ = trickle_circuit(species_vals_t, reactions_en, out_maps)
            # print("out is: ", out_)  
            if out is not None:
                assert out_ == out, "The outputs are different for different initial conditions! \nprod_assign:      {}\n   -> output {}\nprod_assign_prev: {}\n   -> output {}\n".format(prod_assign,out_, prev_prod_assign,out)
            out = out_
            prev_prod_assign = prod_assign

    else:
        for (specie, x_in) in in_maps:
            species_vals[specie] |= x_ins_concrete[x_in]

        out = trickle_circuit(species_vals, reactions_en, out_maps)

    #print(species)
    # print(out, riedel)
    return out


def verify_manually(circuit, phi_funcs, N_XVARS, riedel=False):
    circuit_outs  = []
    phi_outs = []
    for x_s_concrete in itertools.product((False, True), repeat=N_XVARS):
        circuit_outs.append(evaluate_circuit(circuit, x_s_concrete, riedel=riedel))
        phi_outs.append([f_z3_concrete(phi_func(x_s_concrete)) for phi_func in phi_funcs])
    
    assert circuit_outs == phi_outs, 'Circuit_outs and phi_out mismatch \n{}\n{}\n'.format(circuit_outs, phi_outs)


def get_circuit(model, reactions, in_options, out_species, model_vars, cost = None, printit = False):
    assert model is not None, "Cannot get circuit without a model (unsat)"

    (x_ins, i2x_list, f2o_list, reacts, species) = model_vars

    #print('reacts',reacts)
    reactions_en = [(i, react) for (i, react) in enumerate(reactions) if meval(model,reacts[i])]
    in_open = set(sum([react[0] for (i, react) in reactions_en], ()))
    
    #print(reactions_en)

    in_maps = [(i, i_map.as_long()) for  i, i_map in zip(in_options, meval(model,i2x_list)) if i in in_open and i_map.as_long() != 0]

    if isinstance(f2o_list[0], int):
        out_maps = [out_species[f2o] for f2o in f2o_list]
    else:
        out_maps = [out_species[f2o.as_long()] for f2o in meval(model,f2o_list)]
    cost_ = meval(model, cost)

    if printit:
        gates = [react for react in reactions_en if (len(react[1][0]) > 1 or len(react[1][1]) > 1)]
        wires = [react for react in reactions_en if (len(react[1][0]) == 1 and len(react[1][0]) == 1)]
        print('      enabled gates:', gates)
        print('      enabled wires:', wires)
        print('     ID to logic in:', [(i, x_ins[i_map]) for (i, i_map) in in_maps])
        print('     F to logic out:', [(i, o_map) for (i, o_map) in enumerate(out_maps)])
        print('   cost (G + W + T):', cost_)
        print('')
        
    circuit = (reactions_en, in_maps, out_maps)

    #print(circuit)
    return circuit



# Program synthesis assert (DOES NOT DO CEGIS OR OTHER FANCY SYNTHESIS) 
# Find assignments to z3 variables such that circuits output and function output are ==
# ∃P.∀x. φ(x,P(x))
def smt_model_verify(model, x_vars, out_s, phi_func):
    assert (model != None), 'cannot verify unsat model'

    slvr = Solver()

    phi_f = phi_func(x_vars)
    slvr.add(Not(phi_f == out_s))

    for var in model:
        slvr.add(var() == model[var()])

    #print(slvr.sexpr())
    z3_check = slvr.check()

    if z3_check == sat:
        model = slvr.model()

        vals = [True if model[x] == None else  model[x] for x in x_vars]

        return vals
    else:
        return None


def header_str(num_tests = 2):
    toprint = 'FX'
    for i in range(num_tests): 
        toprint += ",t{},c{}".format(i, i)
    toprint += '\n'
    return toprint

def record_str(r, f_num = 1, header = False):
    if f_num == 1:
        f_i, times, costs = r[0], r[1::2], r[2::2]
        f_is = [f_i]
    elif f_num == 2:
        f_i0, f_i1, times, costs = r[0], r[1], r[2::2], r[3::2]
        f_is = [f_i0, f_i1]
    else:
        print("ERROR: f_num must be 1 or 2 - or you need to update this function")
        exit(1)
    

    if header:
        toprint = header_str(len(times))
    else:
        toprint = ""

    #toprint += f_i.__str__()
    toprint += ",".join([f_i.__str__() for f_i in f_is])
    for t, c in zip(times, costs): 
        toprint += ",{:.2f},{}".format(t, c)
    toprint += '\n'
    return toprint

def dump_records(records, f_num = 1, filename = '', flat = False):
    toprint = ""
    if flat:
        for r in records:
            toprint += record_str(r, f_num=f_num)
    else:
        for rr in records:
            for r in rr:
                toprint += record_str(r, f_num=f_num)
                
    if filename == '':
        print(toprint, end='')
    else:
        with open(filename, "a") as g:
            fcntl.flock(g, fcntl.LOCK_EX)
            g.write(toprint)
            fcntl.flock(g, fcntl.LOCK_UN)



def concretize(expr, vars, var_vals):
    return simplify(substitute(expr, *zip(vars, [BoolVal(x) for x in var_vals])))

def forsome_slvr_assume_assert(slvr, x_vars, in_examples, outs_f, phi_funcs, constraints, forall_vars):
    
    if constraints is not None:
        slvr.add(constraints)

    phis = [phi_func(x_vars) for phi_func in phi_funcs]


    # all_ins = list(itertools.product((False, True), repeat=len(x_vars)))
    forall_vars_cases = list(itertools.product((False, True), repeat=len(forall_vars)))
    # print(forall_vars)
    # print(forall_vars_cases)


    # print(forall_vars_cases)
    method1 = True
    if method1:
        # query = simplify(And([ simplify(concretize(out_s, x_vars + forall_vars, in_ex + vars_val) == concretize(phi, x_vars, in_ex))
        #                     for vars_val in forall_vars_cases
        #                     for in_ex in in_examples
        #                     for out_s, phi in zip(outs_f, phis) ] ))
        queries = [ simplify(concretize(out_s, x_vars + forall_vars, in_ex + vars_val) == concretize(phi, x_vars, in_ex))
                            for vars_val in forall_vars_cases
                            for in_ex in in_examples
                            for out_s, phi in zip(outs_f, phis) ]
        for q in queries:
            # slvr.add(simplify(Implies(constraints, q)))
            # slvr.add(Implies(constraints, q))
            slvr.add(q)
        # query = And([ concretize(out_s, x_vars + forall_vars, in_ex + vars_val) == concretize(phi, x_vars, in_ex)
        #                     for in_ex in in_examples
        #                     for vars_val in forall_vars_cases
        #                     for out_s, phi in zip(outs_f, phis) ] )
    else:   
        fulfills_subset = And([concretize(out_s, x_vars, in_ex) == concretize(phi, x_vars, in_ex) 
                            for in_ex in in_examples
                            for out_s, phi in zip(outs_f, phis) ] )

        if forall_vars:
            query = ForAll(forall_vars, fulfills_subset)
        else: 
            query = fulfills_subset
        slvr.add(Implies(constraints, query))

    # print(fulfills_subset)
    # slvr.add(simplify(Implies(constraints, query)))
    # slvr.add(query)


def run_slvr(slvr, z3out='', z3outsoln=''):
    z3_check = slvr.check()

    if z3out != '':
        with open(z3out+'.smt2', 'w') as text_file:
            print(slvr.sexpr(), file=text_file)

    if z3_check == sat:
        if z3outsoln != '':
            with open(z3outsoln, 'w') as text_file:
                print(slvr.model().sexpr(), file=text_file)

        return slvr.model()
    else:
        return None


# What about for UNSAT?
def synth1(x_vars, outs_f, phi_funcs, constraints, forall_vars, debug=False, z3out='', z3outsoln=''):
    all_ins = list(itertools.product((False, True), repeat=len(x_vars)))
    slvr = Solver()

    forsome_slvr_assume_assert(slvr, x_vars, all_ins, outs_f, phi_funcs, constraints, forall_vars)
    return run_slvr(slvr, z3out=z3out, z3outsoln=z3outsoln)


def minimize_sys(cost_minimize, x_vars, outs_f, phi_funcs, constraints, forall_vars, z3out='', z3outsoln=''):
    all_ins = list(itertools.product((False, True), repeat=len(x_vars)))
    slvr = Optimize()
    
    forsome_slvr_assume_assert(slvr, x_vars, all_ins, outs_f, phi_funcs, constraints, forall_vars)
    for cost in cost_minimize:
        slvr.minimize(cost)
    return run_slvr(slvr, z3out=z3out, z3outsoln=z3outsoln)



def run_test_inv_1f(f_i, f_i_len=1, riedel=False, inv_function=get_inv_19g_27w, filename='', N_XVARS=4, verif=True, progressbar=False, print_delay = True, printit=False):

    (inv_name, reactions, in_species, out_species, inputs_distinct) = inv_function()
    
    nF = 1
    
    if inv_function == get_inv_4G_complete_cyclic or inv_function == get_inv_3G_complete_cyclic:
        (x_vars, outs_f, constraints, cost, cost_minimize, model_vars, forall_vars) = setup(reactions, in_species, out_species, N_XVARS, nF, inputs_distinct, riedel=riedel, force_f2o = [0,1])
    else:
        (x_vars, outs_f, constraints, cost, cost_minimize, model_vars, forall_vars) = setup(reactions, in_species, out_species, N_XVARS, nF, inputs_distinct, riedel=riedel)

    records = []
    for f_i_ in tqdm(range(f_i, f_i+f_i_len), disable = not progressbar, total=f_i_len):

        phi_f = lambda xvars: phi_func_i(f_i_, xvars)

        start = time.time()
        m1 = synth1(x_vars, outs_f, [phi_f], constraints, forall_vars)
        # print(m1)
        t1 = time.time() - start
        c1 = meval_long(m1, cost)
        if m1 != None and verif:
            circ1 = get_circuit(m1, reactions, in_species, out_species, model_vars, cost=cost, printit=printit)
            verify_manually(circ1, [phi_f], N_XVARS, riedel=False)

        start = time.time()
        m2 = minimize_sys(cost_minimize, x_vars, outs_f, [phi_f], constraints, forall_vars)
        t2 = time.time() - start
        c2 = meval_long(m2, cost)
        if m1 != None and verif:
            circ2 = get_circuit(m2, reactions, in_species, out_species, model_vars, cost=cost, printit=printit)
            verify_manually(circ2, [phi_f], N_XVARS, riedel=False)

        records.append((f_i_, t1, c1, t2, c2))
        if not print_delay:
            print(record_str(records[-1], f_num=nF, header=False), end='')


    if print_delay:
        dump_records(records, f_num=nF, filename = filename, flat = True)
    #return records




def run_test_inv_2f(f_i0, f_i1=-1, f_i1_len=-1, riedel=False, inv_function=get_inv_2g_small_acyclic, filename='', N_XVARS=3, verif=True, printit=False, progressbar=False, print_delay = True, opt=True):
    assert (N_XVARS == 3), "currently not written for N_XVARS > 3"
    
    if f_i1 == -1:
        f_i1 = f_i0 + 1
    if f_i1_len == -1:
        f_i1_len = 256 - f_i1
    
    assert (f_i1 < 256), "can't go past 256 3-bit function! max len if f_i={} is {}".format(f_i1, 256-f_i1)

    (inv_name, reactions, in_species, out_species, inputs_distinct) = inv_function()
    
    nF = 2

    if inv_function == get_inv_4G_complete_cyclic or inv_function == get_inv_3G_complete_cyclic:
        (x_vars, outs_f, constraints, cost, cost_minimize, model_vars, forall_vars) = setup(reactions, in_species, out_species, N_XVARS, nF, inputs_distinct, riedel=riedel, force_f2o = [0,1])
    else:
        (x_vars, outs_f, constraints, cost, cost_minimize, model_vars, forall_vars) = setup(reactions, in_species, out_species, N_XVARS, nF, inputs_distinct, riedel=riedel)
    
    
    records = []
    #print('----', f_i0, list(range(f_i1, f_i1+f_i1_len)))
    for f_i1_ in tqdm(range(f_i1, f_i1+f_i1_len), disable = not progressbar, total=f_i1_len):
        
        phi0_f = lambda xvars: phi_func_i(f_i0, xvars)
        phi1_f = lambda xvars: phi_func_i(f_i1_, xvars)
        phi_fs = [phi0_f, phi1_f]

        start = time.time()
        m1 = synth1(x_vars, outs_f, phi_fs, constraints, forall_vars)
        # print(m1)
        t1 = time.time() - start
        c1 = meval_long(m1, cost)
        if m1 != None and verif:
            circ1 = get_circuit(m1, reactions, in_species, out_species, model_vars, cost=cost, printit=printit)
            (reactions_en, in_maps, out_maps) = circ1

            # print("reactions_en: {}".format(reactions_en))
            # print("in_maps: {}".format(in_maps))
            # print("out_maps: {}".format(out_maps))

            verify_manually(circ1, phi_fs, N_XVARS, riedel=False)

        if opt:
            start = time.time()
            m2 = minimize_sys(cost_minimize, x_vars, outs_f, phi_fs, constraints, forall_vars)
            t2 = time.time() - start
            c2 = meval_long(m2, cost)
            if m1 != None and verif:
                circ2 = get_circuit(m2, reactions, in_species, out_species, model_vars, cost=cost, printit=printit)
                verify_manually(circ2, phi_fs, N_XVARS, riedel=False)
            records.append((f_i0, f_i1_, t1, c1, t2, c2))
        else:
            records.append((f_i0, f_i1_, t1, c1))
        #print(record_str(records[-1], f_num=nF, header=False), end='')
        if not print_delay:
            print(record_str(records[-1], f_num=nF, header=False), end='')


    if print_delay:
        dump_records(records, f_num=nF, filename = filename, flat = True)
    #return records


def run_test_inv_2f_all(inv_function, filename='results.csv', start_fi0 = 0, upto=255, processes=1, display_progress = True, opt=True, print_delay = True, riedel=False):
    N_XVARS = 3
    #total_fi = 2**2**N_XVARS
    assert upto < 2**2**N_XVARS, "upto of {} is too big! must be < 255".format(upto)
    if start_fi0 == 0:
        f = open(filename, "w")
        if opt:
            f.write("f_i0,f_i1,t1,c1,t2,c2\n")
        else:
            f.write("f_i0,f_i1,t1,c1\n")
        f.close()
    else:
        f = open(filename, "a")
        f.write("\n")
        f.close()

    f_i0s = range(start_fi0, upto)
    #print(list(f_i0s))
    #f_i2 = range(start_fi0, total_fi) #fi2 will start here, and do

    run_test_p = partial(run_test_inv_2f, inv_function=inv_function, filename=filename, N_XVARS=N_XVARS, opt=opt, print_delay = print_delay,riedel=riedel)

    if processes == 1:
        for fi0 in tqdm(f_i0s, disable = not display_progress, total=upto):
            run_test_p(fi0)
    else:
        pool = Pool(processes=processes)
        if display_progress:
            for _ in tqdm(pool.imap(run_test_p, f_i0s), total=upto, initial=start_fi0):
                pass
        else:
            for _ in pool.imap(run_test_p, f_i0s):
                pass


# inventory_test_all_funcs(get_inv_19g_27w, filename='results.csv', start_i = 0, processes=4, N_XVARS = 4, save_chunks = 512)
def inventory_test_all_funcs(inv_function, filename='results.csv', start_i = 0, processes=4, N_XVARS = 4, save_chunks = 512, display_progress = True, verif=True):

    total_fi = 2**2**N_XVARS
    print("total_fi: {}".format(total_fi))
    if start_i == 0:
        f = open(filename, "w")
        #f.write("f_i,t1,c1,t2,c2\n")
        f.write("FX,ex_sec,ex_cost,opt_sec,opt_cost\n")
        f.close()
    else:
        f = open(filename, "a")
        f.write("\n")
        f.close()

    
    f_i = range(start_i, total_fi, save_chunks)

    run_test_p = partial(run_test_inv_1f, f_i_len=save_chunks, inv_function=inv_function, filename=filename, N_XVARS=N_XVARS, verif=verif)

    # pool = Pool(processes=processes)

    # if display_progress:
    #     for _ in tqdm(pool.imap(run_test_p, f_i), total=total_fi//save_chunks, initial=start_i//save_chunks):
    #         pass
    # else:
    #     pool.imap(run_test_p, f_i)

    #    f_i = range(start_i, total_fi, save_chunks)

    # run_test_p = partial(run_test_inv_1f, f_i_len=save_chunks, inv_function=inv_function, filename=filename, N_XVARS=N_XVARS)



    if processes == 1:
        for fi in tqdm(f_i, disable = not display_progress, total=total_fi//save_chunks):
            run_test_p(fi)
    else:
        pool = Pool(processes=processes)
        if display_progress:
            for _ in tqdm(pool.imap(run_test_p, f_i), total=total_fi//save_chunks, initial=start_i//save_chunks):
                pass
        else:
            for _ in pool.imap(run_test_p, f_i):
                pass
    return



ymin_plt = -.05

def highlightpoint(plt, x_list, y_list, y_value, x_adj, y_adj, just_x = False, just_y = False, x_postfix=''):
    (x_val, y_val) = min(zip(x_list, y_list), key=lambda xy: abs(xy[1] - y_value))

    if not just_x and not just_y:
        plt.annotate("{:.2f}{},{:.2f}".format(x_val, x_postfix, y_val), xy=(x_val, y_val), xytext=(x_val+x_adj, y_val+y_adj),color='r', fontsize=9)
    if just_x:
        plt.annotate("{:.2f}{}".format(x_val, x_postfix), xy=(x_val, y_val), xytext=(x_val+x_adj, y_val+y_adj), color='r', fontsize=9)
    if just_y:
        plt.annotate("{:.2f}".format(y_val), xy=(x_val, y_val), xytext=(x_adj, y_val+y_adj), color='r', fontsize=9)

    plt.hlines(y=y_val, xmin=0, xmax=x_val, linewidth=1.5, linestyles=':', color='r')
    plt.vlines(x=x_val, ymin=ymin_plt, ymax=y_val, linewidth=1.5, linestyles=':', color='r')


def labelpoint(plt, x_list, y_list, y_value, x_adj, y_adj, message):
	(x_val, y_val) = min(zip(x_list, y_list), key=lambda xy: abs(xy[1] - y_value))
	plt.annotate("{}".format(message), xy=(x_val, y_val), xytext=(x_val+x_adj, y_val+y_adj),color='r', fontsize=9)
	plt.hlines(y=y_val, xmin=0, xmax=x_val, linewidth=1.5, linestyles=':', color='r')
	plt.vlines(x=x_val, ymin=ymin_plt, ymax=y_val, linewidth=1.5, linestyles=':', color='r')


def cdf_plot_time(csv_file, inv_name, n_xvars):

    data = read_csv(csv_file)
    fxs = data['FX'].tolist()
    exist_time = data['ex_sec'].tolist()
    exist_cost = data['ex_cost'].tolist()
    opt_time = data['opt_sec'].tolist()
    opt_cost = data['opt_cost'].tolist()

    PLOT_TITLE = 'Runtime: {}, All {}-bit Predicates'.format(inv_name, n_xvars)

    unsat_inds = [i for i, x in enumerate(exist_cost) if np.isnan(x)]
    sat_inds = list(set(range(len(exist_cost))).difference(unsat_inds))

    N = len(exist_cost)
    N_US = len(unsat_inds)
    N_S = len(sat_inds)
    #print(N_US)

    # sort the data in ascending order
    x_exist    = sorted(exist_time)
    x_exist_S  = sorted([exist_time[i] for i in sat_inds])

    x_opt    = sorted(opt_time)
    x_opt_S  = sorted([opt_time[i] for i in sat_inds])

    if N_US > 0:
        x_exist_US = sorted([exist_time[i] for i in unsat_inds])
        x_opt_US = sorted([opt_time[i] for i in unsat_inds])

    # get the cdf values of y
    y    = [float(i)/float(N-1) for i in range(N)]
    y_S  = [float(i)/float(N_S-1) for i in range(N_S)]
    y_US = [float(i)/float(N_US-1) for i in range(N_US)] 


    #plt.figure()

    plt.figure(figsize=(10, 5))
    plt.rcParams["font.weight"] = "bold"
    plt.rcParams["axes.labelweight"] = "bold"

    plt.title(PLOT_TITLE, fontname="DejaVu Sans",fontweight="bold")

    # plotting
    plt.xlabel('Runtime [CPU seconds]')
    plt.ylabel('P(solve)')


    exist = True
    opt=  True
    if exist:
        plt.plot(x_exist_S, y_S  , color = 'firebrick',     label = "Existence", linewidth=3)
        highlightpoint(plt, x_exist_S, y_S, 0.5, 0.018, -0.01, just_y = True)
        highlightpoint(plt, x_exist_S, y_S, 0.5, -0.019, .009, just_x = True, x_postfix='s')
        highlightpoint(plt, x_exist_S, y_S, 0.99, -.05, .02, just_x = True, x_postfix='s')

    if opt:
        line2 = plt.plot(x_opt_S, y_S    , color = 'green', linestyle='dashed' ,    label = "Optimality", linewidth=3)    
        # line = line2.pop(0)
        # line.remove()
        highlightpoint(plt, x_opt_S, y_S, 0.99, 0.018, -0.04, just_y = True)
        highlightpoint(plt, x_opt_S, y_S, 0.5, -0.16, .009, just_x = True, x_postfix='s')
        highlightpoint(plt, x_opt_S, y_S, 0.99, -.18, .02, just_x = True, x_postfix='s')



    if N_US > 0:
        plt.plot(x_exist_US, y_US, linestyle='dashed' , color = 'midnightblue', label = "UNSAT")
        highlightpoint(plt, x_exist_US, y_US, 0.5, -.09, .007, just_x = True, x_postfix='s')
        highlightpoint(plt, x_exist_US, y_US, 0.99, -.09, .02, just_x = True, x_postfix='s')

    plt.xscale('log',base=2, ) 
    plt.legend(loc='lower right')
    plt.ylim(ymin=ymin_plt)

    # ax = plt.gca()
    # fix axis tixks at 2^-4 to 2^ 8, evens only
    # ax.set_xticks([2**i for i in range(-4, 9, 2)])
    
    print('... Saving ./runtime_cdf.pdf ...')
    plt.savefig('runtime_cdf.pdf')
    # plt.show()
