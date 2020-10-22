# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    sub_map = {'-&': Formula.parse("~(p&q)"), '-|': Formula.parse("~(p|q)"), '+': Formula.parse("(~(p&q)&(p|q))"),
               '->':Formula.parse("~(p&~q)"), '<->': Formula.parse("((p|~q)&(~p|q))")}
    return formula.substitute_operators(sub_map)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    sub_map = {'-&': Formula.parse("~(p&q)"), '-|': Formula.parse("(~p&~q)"), '+': Formula.parse("(~(p&q)&~(~p&~q))"),
               '->':Formula.parse("~(p&~q)"), '<->': Formula.parse("~(~(p&q)&~(~p&~q))"), '|': Formula.parse("~(~p&~q)")}
    return to_not_and_or(formula).substitute_operators(sub_map)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    sub_map = {'~': Formula.parse("(p-&p)"), '&': Formula.parse("((p-&q)-&(p-&q))"),
               '|': Formula.parse("((p-&p)-&(q-&q))"), '+': Formula.parse("((p-&(p-&q))-&(q-&(p-&q)))"),
               '-|': Formula.parse("(((p-&p)-&(q-&q))-&((p-&p)-&(q-&q)))"),
               '->': Formula.parse("(p-&(q-&q))"),
               '<->': Formula.parse("(((p-&(p-&q))-&(q-&(p-&q)))-&((p-&(p-&q))-&(q-&(p-&q))))")}

    return formula.substitute_operators(sub_map)



def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    sub_map = {'-&': Formula.parse("(p->~q)"), '&': Formula.parse("~(p->~q)"), '|': Formula.parse("((p->~p)->~(q->~q))"),
               '-|': Formula.parse("~((p->~p)->~(q->~q))"), '+': Formula.parse("((p->~(p->~q))->~(q->~(p->~q)))"),
               '<->': Formula.parse("~((p->~(p->~q))->~(q->~(p->~q)))")}
    # return to_nand(f).substitute_operators(sub_map)
    return formula.substitute_operators(sub_map)

if __name__ == '__main__':
    # sub_map = {'-&': Formula.parse("~(p&q)"), '-|': Formula.parse("(~p&~q)"), '+': Formula.parse("(~(p&q)&~(~p&~q))"),
    #            '->': Formula.parse("~(p&~q)"), '<->': Formula.parse("~(~(p&q)&~(~p&~q))"),
    #            '|': Formula.parse("~(~p&~q)")}
    # for key in sub_map:
    #     print(key)
    #     print_truth_table(sub_map[key])
    arr = [Formula.parse("(p&q)"), Formula.parse("(p-&q)"), Formula.parse("(p|q)"), Formula.parse("(p-|q)"),
            Formula.parse("(p+q)"), Formula.parse("(p<->q)")]
    for f in arr:
        f1 = to_implies_not(f)
        print_truth_table(f1)
        print("the good one: ")
        print_truth_table(f)
        print("_______________________________________")


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
