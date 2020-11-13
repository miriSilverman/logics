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
    # print("formula is: ", formula)
    if is_relation(formula.root):

        new_args_names = []     # R[g(x),y,h(k(x3))] ---> R[z1,y,z3]
        all_formulas = []       # [[z1=g(x)],???, [z2=k(x3), z3=h(z2)]]
        all_formulas_as_relations = []  # [G(z1,x), K(z2,x3), H(z3,z2)]
        for term in formula.arguments:
            if is_function(term.root):
                formulas = _compile_term(term)
                # print("formulas: ", formulas)
                all_formulas += [formulas]
                new_args_names.append(formulas[-1].arguments[0])
            else:
                new_args_names.append(term)
        # print("new_args_names: ", new_args_names)
        # print("all_formulas: ", all_formulas)

        for list in all_formulas:
            # print("cur list: ", list)
            for form in list:
                print("cur form: ", form)
                if is_equality(form.root):
                    name = function_name_to_relation_name(form.arguments[1].root)
                    # print("name: ", name)
                    print(form.arguments[0])
                    print(type(form.arguments[0]))
                    print("args: f", form.arguments[1].arguments)
                    args = (form.arguments[0],)+form.arguments[1].arguments
                    # print(args)
                    relation = Formula(name, args)
                    print("type of args: ", type(args[0]))
                    print("relation ",relation)
                    all_formulas_as_relations.append(relation)
                # else:
        basic_relation = Formula(formula.root, new_args_names)
        new_f = concat_relations(0, all_formulas_as_relations,basic_relation)
        # print(new_f)
        return new_f
    # elif is_equality(formula.root):
    #     name = function_name_to_relation_name(formula.root)
    #     arg1 = formula.arguments[0]
    #     arg2 = formula.arguments[1]
    #     first = _compile_term(arg1) if is_function(arg1.root) else arg1.root
    #     second = _compile_term(arg2) if is_function(arg2.root) else arg2.root
    #     return Formula(name, )

def concat_relations(idx, all_relations, basic_relation) -> Formula:
    if idx == len(all_relations):
        return basic_relation
    cur_relation = all_relations[idx]
    var = cur_relation.arguments[0]
    next_formula = Formula('&', cur_relation, concat_relations(idx+1, all_relations, basic_relation))
    return Formula('E', str(var), next_formula)


if __name__ == '__main__':
    # relations = [Formula.parse("G(z1,x)"), Formula.parse("K(z2,x3)"), Formula.parse("H(z3,z2)")]
    # f = concat_relations(0, relations, Formula.parse("R(z1,y,z3)"))
    # print(f)
    form = Formula.parse("R(f(g(x)),h(2,y),3)")
    f = replace_functions_with_relations_in_formula(form)
    print(f)






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
