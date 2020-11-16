# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *
import copy


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Returns:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1
    relations = copy_dict(model.relation_meanings)  # copies the relations from the models relations

    for func in model.function_meanings:
        new_name = function_name_to_relation_name(func)

        new_relations_set = set()
        meaning_keys = model.function_meanings[func]
        for key in meaning_keys:
            tup = [v for v in meaning_keys[key]]
            for i in key:
                tup.append(i)
            new_relations_set.add(tuple(tup))
        relations[new_name] = new_relations_set

    return Model(model.universe, model.constant_meanings, relations, {})


def copy_dict(dict_to_copy):
    """
    deepcopy of dictionary of {str: set}
    :param dict_to_copy: the dictionary to copy
    :return: a copy of the dictionary
    """
    new_dict = {}
    for key in dict_to_copy:
        new_set = set()
        for tup in dict_to_copy[key]:
            new_set.add(tup)
        new_dict[key] = new_set
    return new_dict


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2
    relations = copy_dict(model.relation_meanings)  # copies the relations from the models relations
    funcs = {}      # {func name: {(combination of elements in universe) : their evaluation}}

    for func in original_functions:
        new_name_of_func = function_name_to_relation_name(func)

        if new_name_of_func not in model.relation_meanings: # the function doesnt exist in the relations
            return None


        func_meaning_dict = {}  # dict of {tuple of elements from the universe : their evaluation (from the universe)}
                                # i.e {('b','a') : 'a'}
        meaning_of_relation = model.relation_meanings[new_name_of_func]

        # not the right number of combinations of elements in the universe
        if len(meaning_of_relation) != len(model.universe)**(model.relation_arities[new_name_of_func]-1):
            return None

        for tup in meaning_of_relation:
            key = tup[1:]
            val = tup[0]
            if key in func_meaning_dict:    # there is already a value to the current key
                return None
            func_meaning_dict[key] = val

        funcs[func] = func_meaning_dict
        relations.pop(new_name_of_func)     # removing the relation that represents a func from the relations

    return Model(model.universe, model.constant_meanings, relations, funcs)


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert variable[0] != 'z'
    # Task 8.3
    formulas = []
    new_args = []       # args converted to variables
    for old_arg in term.arguments:
        if is_function(old_arg.root):
            args_formulas = _compile_term(old_arg)      # [zi = g(x), ....]
            formulas += args_formulas
            name_of_new_arg = args_formulas[-1].arguments[0]    # the last equation contains the new name of the
                                                                # old function
            new_args.append(name_of_new_arg)
        else:
            new_args.append(old_arg)

    new_name = next(fresh_variable_name_generator)  #generates new name
    new_formula = Formula('=', [Term(new_name), Term(term.root, new_args)])
    formulas.append(new_formula)
    return formulas




def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4
    if is_unary(formula.root):
        return Formula('~', replace_functions_with_relations_in_formula(formula.first))

    elif is_binary(formula.root):
        first = replace_functions_with_relations_in_formula(formula.first)
        second = replace_functions_with_relations_in_formula(formula.second)
        return Formula(formula.root, first, second)

    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))

    elif is_relation(formula.root) or is_equality(formula.root):

        new_args_names = []     # R[g(x),y,h(k(x3))] ---> R[z1,y,z3]
        all_formulas = []       # [z1=g(x), z2=k(x3), z3=h(z2)]
        all_formulas_as_relations = []  # [G(z1,x), K(z2,x3), H(z3,z2)]

        for term in formula.arguments:
            if is_function(term.root):
                formulas = _compile_term(term)      # all the relevant equations
                all_formulas.extend(formulas)
                new_args_names.append(formulas[-1].arguments[0])    # adds the final var that represents the function
            else:
                new_args_names.append(term)     # adds the constant or the variable

        for form in all_formulas:
            name = function_name_to_relation_name(form.arguments[1].root)
            args = (form.arguments[0],) + form.arguments[1].arguments
            relation = Formula(name, args)
            all_formulas_as_relations.append(relation)

        original_formula = Formula(formula.root, new_args_names)
        new_f = concat_relations(0, all_formulas_as_relations, original_formula)
        return new_f


def concat_relations(idx, all_relations, basic_relation) -> Formula:
    """
    concatenate the relations in all_relations to the format:
    E z_i [F(z_i, x1,...,xn) & E z_j G(z_j, y1,...,yn)&...basic_relation]
    :param idx: index of the current relation to concatenate
    :param all_relations: list of all the relations to concatenate in the format
    :param basic_relation: the final relation to add at the end
    """
    if idx == len(all_relations):
        return basic_relation
    cur_relation = all_relations[idx]
    var = cur_relation.arguments[0]
    next_formula = Formula('&', cur_relation, concat_relations(idx+1, all_relations, basic_relation))
    return Formula('E', str(var), next_formula)





def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5
    new_formulas = set()
    for formula in formulas:
        new_formula = replace_functions_with_relations_in_formula(formula)
        new_formulas.add(new_formula)

        # all the names of the relations in the new formula that are a conversion of a function
        old_funcs_as_relations =  [(function_name_to_relation_name(f[0]), f[1]+1) for f in formula.functions()]

        for relation, arg_num in old_funcs_as_relations:
            args_for_R = [Term('x' + str(i)) for i in range(arg_num)]   # [x0, x1, ... , xn]

            basic_formula = Formula('E', args_for_R[0].root, Formula(relation, args_for_R)) # "Ex0[R(x0,...,xn)]"
            f1 = first_constrain(args_for_R, 1, basic_formula)  # "Ax1[Ax2[...Axn[Ex0[R(x0,...,xn)]]]]"

            z1, z2 = Term('z1'), Term('z2')
            args_for_R.extend([z1, z2])


            # "((R(z1, x1,...,xn)&R(z2, x1,...,xn))->z1=z2)"
            basic_formula = Formula('->', Formula('&', Formula(relation, [z1] + args_for_R[1:-2]),
                                                  Formula(relation, [z2] + args_for_R[1:-2])), Formula('=', [z1, z2]))
            # "Ax1[Ax2[...Axn[Az1[Az2[ ((R(z1, x1,...,xn)&R(z2, x1,...,xn))->z1=z2) ]]]]]"
            f2 = first_constrain(args_for_R, 1, basic_formula)


            conj_of_constrains = Formula('&', f1, f2)
            final = Formula('&', new_formula, conj_of_constrains)
            new_formulas.add(final)

        return new_formulas


def first_constrain(args_for_R, idx, basic_formula):
    """
    :param args_for_R: list of argument to the relation as x_i
    :param idx: index of the current iteration
    :param relation_name: the relations name
    :return: the formula:
    "Ax1...[Axn[basic_formula]]"
    """
    args_len = len(args_for_R)
    if idx < args_len:
        return Formula('A', args_for_R[idx].root, first_constrain(args_for_R, idx+1, basic_formula))
    else:
        return basic_formula



def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6
    all_relations_in_formulas = relations_in_all_formulas(formulas) # list of all the relations in formulas

    # list of all the formulas when every equality x=y is replaced with SAME(x,y)
    formulas_without_eq = replace_equality_with_same(all_relations_in_formulas, formulas)

    # set of formulas for every relation of type: "Ax[Ay[(SAME(x,y)->(R(x)->R(y))]]"
    fs = eq_replaces(all_relations_in_formulas)

    return set(formulas_without_eq).union(basic_properties_of_same()).union(fs)


def replace_equality_with_same(all_relations_in_formulas, formulas):
    """
    :param all_relations_in_formulas: list of all the relations in all the formulas
    :param formulas: set of all the formulas
    :return: list of all the formulas when every equality x=y is replaced with SAME(x,y)
    """
    formulas_without_eq = []
    for formula in formulas:
        new_formula = replace_equality_helper(formula)
        formulas_without_eq.append(new_formula)
    return formulas_without_eq


def relations_in_all_formulas(formulas):
    """
    :param formulas: set of formulas
    :return: list of all the relations in all the formulas
    """
    all_relations_in_formulas = []
    for f in formulas:
        for r in f.relations():
            all_relations_in_formulas.append(r)
    return all_relations_in_formulas

#
# def print_set(s):
#     for n, i in enumerate(s):
#         print(str(n)+')  ', i)

def replace_equality_helper(formula) -> Formula:
    """
    :param formula: formula to replace the equalities in it
    :return: the formula when every equality x=y is replaced with SAME(x,y)
    """
    root = formula.root
    if is_equality(root) or is_relation(root):
        if is_equality(root):
            root = 'SAME'
        return Formula(root, formula.arguments)
    elif is_quantifier(root):
        return Formula(root, formula.variable, replace_equality_helper(formula.predicate))
    elif is_binary(root):
        first = replace_equality_helper(formula.first)
        second = replace_equality_helper(formula.second)
        return Formula(root, first, second)
    elif is_unary(root):
        first = replace_equality_helper(formula.first)
        return Formula(root, first)

def eq_replaces(relations):
    """
    :param relations: list of all the relations in the formulas
    :return: a set of formulas, each for every relation R(x) of the format:
    "Ax[Ay[(SAME(x,y)->(R(x)->R(y))]]" (as well as for not unary relations)
    """
    formulas = set()
    for relation, arg_num in relations:
        args_for_R1 = [Term('x'+str(i)) for i in range(arg_num)]
        args_for_R2 = [Term('y'+str(i)) for i in range(arg_num)]
        f = concat_alls(args_for_R1, args_for_R2, 0, relation)
        formulas.add(f)
    return formulas

def implies_Rs(args_for_R1, args_for_R2, relation_name):
    """
    :param args_for_R1: list of argument to the relation as x_i
    :param args_for_R2: list of argument to the relation as y_i
    :param relation_name: the relations name
    :return: the formula "(R(x0,...,xn)->R(y0,...,yn))"
    """
    return Formula('->', Formula(relation_name, args_for_R1), Formula(relation_name, args_for_R2))


def conjunc_sames(args_for_R1, args_for_R2, idx):
    """
    :param args_for_R1: list of argument to the relation as x_i
    :param args_for_R2: list of argument to the relation as y_i
    :param idx: index of the current iteration
    :return: the formula: "(SAME(x1, y1)&SAME(x2, y2)&...SAME(xn, yn)"
    """
    f = Formula('SAME', [args_for_R1[idx], args_for_R2[idx]])
    if idx < len(args_for_R1) - 1:
        return Formula('&', f, conjunc_sames(args_for_R1,args_for_R2, idx+1))
    else:
        return f

def concat_alls(args_for_R1, args_for_R2, idx, relation_name):
    """
    :param args_for_R1: list of argument to the relation as x_i
    :param args_for_R2: list of argument to the relation as y_i
    :param idx: index of the current iteration
    :param relation_name: the relations name
    :return: the formula:
    "Ax1...[Axn[Ay1...[Ayn[(SAME(x1, y1)&SAME(x2, y2)&...SAME(xn, yn)->(R(x0,...,xn)->R(y0,...,yn))]]]]"
    """
    args_len = len(args_for_R1)
    if idx < args_len:
        return Formula('A', args_for_R1[idx].root, concat_alls(args_for_R1, args_for_R2, idx+1, relation_name))
    elif idx < args_len*2:
        return Formula('A', args_for_R2[idx-args_len].root, concat_alls(args_for_R1, args_for_R2, idx+1, relation_name))
    else:
        f1 = conjunc_sames(args_for_R1, args_for_R2, 0)
        f2 = implies_Rs(args_for_R1, args_for_R2, relation_name)
        return Formula('->', f1, f2)


def basic_properties_of_same():
    """
    :return:  reflexivity, symmetry, transitivity formulas for SAME
    """
    x = Term('x')
    y = Term('y')
    z = Term('z')
    first = Formula('SAME', [x, y])
    second = Formula('SAME', [y, x])
    mid1 = Formula('SAME', [x, z])
    mid2 = Formula('SAME', [z, y])
    assumptions = Formula('&', mid1, mid2)


    reflexivity = Formula('SAME', [x, x])
    symmetry = Formula('&', Formula('->', first, second), Formula('->', second, first))
    transitivity = Formula('->', assumptions, first)
    return {reflexivity, symmetry, transitivity}


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Returns:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7
    relation_meaning = copy_dict(model.relation_meanings)
    relation_meaning['SAME'] = {(i,i) for i in model.universe}
    return Model(model.universe, model.constant_meanings, relation_meaning)


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
    new_universe = set(model.universe)
    equivalence_classes = {i:i for i in model.universe}
    # print("1:", equivalence_classes)
    for pair in model.relation_meanings['SAME']:
        first, second = pair[0], pair[1]
        if first != second:
            # print("pair: ", pair)
            if first in new_universe and second in new_universe:
                new_universe.remove(second)
                equivalence_classes[first] = first
                equivalence_classes[second] = first
                for key in equivalence_classes:
                    if equivalence_classes[key] == second:
                        equivalence_classes[key] = first


        # print("eq: ",new_universe)
    # print("eq_belonging: ",equivalence_classes)
    constants = dict()
    cm = model.constant_meanings
    for key in cm:
        constants[key] = equivalence_classes[cm[key]]

    relations = dict()
    rm = model.relation_meanings
    for key in rm:
        meanings = set()
        for tup in rm[key]:
            new_tup = []
            for i in tup:
                new_tup.append(equivalence_classes[i])
            meanings.add(tuple(new_tup))
        relations[key] = meanings
    m =  Model(new_universe, constants, relations)
    print(m)
    return m
if __name__ == '__main__':
    # f = Formula.parse("((R(x)&(K(x,y)->G(x1,x2,x3)))&x=y)")
    # replace_equality_with_SAME_in_formulas({f})
    eq = {0,1,2,3,4}
    not_to_add = set()
    same_pairs = {(0,0),(0,4),(1,1),(2,2),(3,3),(4,4),(4,0),(1,2),(2,1)}
    for pair in same_pairs:
        print(pair)
        print(eq)
        p0, p1 = pair[0], pair[1]
        first_in_eq = p0 in eq
        second_in_eq = p1 in eq
        print(first_in_eq)
        print(second_in_eq)
        if p0 != p1:
            print("not equal")
            if first_in_eq and second_in_eq:
                print("here")
                eq.remove(p1)

            # if p0 in eq and p1 in eq:

            # if first_in_eq and second_in_eq:
            #     eq.remove(pair[1])
            # elif not first_in_eq and not second_in_eq:
            #     if first_in_n2add or second_in_n2add:
            #         not_to_add.add(p0)
            #         not_to_add.add(p1)
            #     elif
        # if pair[0] not in not_to_add and pair[1] not in not_to_add:
        #     if pair[0] not in eq and pair[1] not in eq:
        #         eq.add(pair[0])
        # not_to_add.add(pair[0])
        # not_to_add.add(pair[1])
        # print("pair is: ", pair)

        # print(eq)
        # print(not_to_add)
        print("________")


