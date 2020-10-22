# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple, Dict
import itertools
from tabulate import tabulate

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def eval_binary(first: bool, second: bool, operator: str) -> bool:
    if operator == '&':
        return first and second
    elif operator == '|':
        return first or second
    elif operator == "->":
        return second or not first
    elif operator == '+':
        return second != first
    elif operator == '<->':
        return first == second
    elif operator == '-&':
        return not (first and second)
    elif operator == '-|':
        return not (first or second)



def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if is_constant(formula.root):
        return True if formula.root == 'T' else False
    elif is_variable(formula.root):
        return model[formula.root]
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_binary(formula.root):
        return eval_binary(evaluate(formula.first, model), evaluate(formula.second, model), formula.root)





def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    arr = []
    var_num = len(variables)
    for i in itertools.product({False, True}, repeat=var_num):
        dict = {}
        for j in range(var_num):
            dict[variables[j]] = i[j]
        arr.append(dict)
    return arr






def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    arr = []
    for model in models:
        arr.append(evaluate(formula, model))
    return arr



def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    variables = list(sorted(formula.variables()))
    assignment_dict = all_models(list(variables))
    assignment_results = list(truth_values(formula, assignment_dict))
    arr = []
    for i, assignment in enumerate(assignment_dict):
        vals = list(assignment.values())
        vals.append(assignment_results[i])
        vals = ['T' if i == True else 'F' for i in vals]
        arr.append(vals)

    variables.append(formula)
    table = tabulate(arr, variables, tablefmt="pipe", stralign="center").replace(":", "-")
    print(table)

# def table_printer(title, content):
#     print("|", end='')
#     for var in title:
#         print(var, "|", end='')
#     print("\n|")
#     for var in title:
#         print('-'*(len(var)+2), '|', end='')
#     for line in content:
#         print("\n|")
#         pr

if __name__ == '__main__':
    sub_map = {'-&': Formula.parse("~(p&q)"), '-|': Formula.parse("~(p|q)"), '+': Formula.parse("(~(p&q)&(p|q))"),
               '->':Formula.parse("~(p&~q)"), '<->': Formula.parse("((p|~q)&(~p|q))")}
    for key in sub_map:
        print(key, " map: ")
        print_truth_table(sub_map[key])


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    variables = list(sorted(formula.variables()))
    assignment_dict = all_models(list(variables))
    for val in truth_values(formula, assignment_dict):
        if not val:
            return False
    return True



def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    return not is_satisfiable(formula)

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    variables = list(sorted(formula.variables()))
    assignment_dict = all_models(list(variables))
    for val in truth_values(formula, assignment_dict):
        if val:
            return True
    return False


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    vars = list(variables(model))
    formula =_synthesize_for_model_helper(model, vars, 0)
    return formula


def _synthesize_for_model_helper(model, vars,  i) -> Formula:
    """
    Args:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.
        vars: list of vars in the model
        i: iteration in vars index

    Returns: The synthesized formula.

    """
    if model[vars[i]]:
        formula =  Formula(vars[i])
    else:
        formula =  Formula('~', Formula(vars[i]))

    if i == len(model) - 1:
        return formula
    return Formula('&', formula, _synthesize_for_model_helper(model, vars, i+1))


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    assignments = all_models(variables)
    for var in variables:
        formula = Formula('&', Formula(var), Formula('~', Formula(var)))
        break
    changed = False
    for val, assignment in zip(values, assignments):
        if val:
            cur_formula = _synthesize_for_model(assignment)
            if not changed:
                formula = cur_formula
                changed = not changed
            else:
                formula = Formula('|', formula, cur_formula)
    return formula



def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variables.

    Parameters:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8
    vars = list(variables(model))
    formula =_synthesize_for_all_except_model_helper(model, vars, 0)
    return formula

def _synthesize_for_all_except_model_helper(model, vars,  i) -> Formula:
    """
    Args:
        model: model over a nonempty set of variables, in which the synthesized
            formula is to hold.
        vars: list of vars in the model
        i: iteration in vars index

    Returns: The synthesized formula.

    """
    if not model[vars[i]]:
        formula =  Formula(vars[i])
    else:
        formula =  Formula('~', Formula(vars[i]))

    if i == len(model) - 1:
        return formula
    return Formula('|', formula, _synthesize_for_all_except_model_helper(model, vars, i+1))

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variables,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variables for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9
    assignments = all_models(variables)
    for var in variables:
        formula = Formula('|', Formula(var), Formula('~', Formula(var)))
        break
    changed = False
    for val, assignment in zip(values, assignments):
        if not val:
            cur_formula = _synthesize_for_all_except_model(assignment)
            if not changed:
                formula = cur_formula
                changed = not changed
            else:
                formula = Formula('&', formula, cur_formula)
    return formula

# Tasks for Chapter 4


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
