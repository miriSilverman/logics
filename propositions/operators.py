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
               '->':Formula.parse("~(p&~q)"), '<->': Formula.parse("((p|~q)&(~p|q))"), 'F': Formula.parse("(p&~p)"),
               'T': Formula.parse("(p|~p)")}
    return formula.substitute_operators(sub_map)

if __name__ == '__main__':
    f = Formula.parse("(q<->(x1<->x2))")
    f = to_not_and_or(f)
    print(f)
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
               '->':Formula.parse("~(p&~q)"), '<->': Formula.parse("~(~(p&q)&~(~p&~q))"),
               '|': Formula.parse("~(~p&~q)"),'F': Formula.parse("(p&~p)"), 'T': Formula.parse("~(p&~p)")}
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
               '<->': Formula.parse("(((p-&(p-&q))-&(q-&(p-&q)))-&((p-&(p-&q))-&(q-&(p-&q))))"),
               'T': Formula.parse("(p-&(p-&p))"), 'F': Formula.parse("((p-&(p-&p))-&(p-&(p-&p)))")}

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
               '<->': Formula.parse("~((p->~(p->~q))->~(q->~(p->~q)))"),
               'T': Formula.parse("(p->p)"), 'F': Formula.parse("~(p->p)")}
    return formula.substitute_operators(sub_map)


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
    sub_map = {'~': Formula.parse("(p->F)"),
               '-&': Formula.parse("(p->(q->F))"), '&': Formula.parse("((p->(q->F))->F)"),
               '|': Formula.parse("((p->(p->F))->((q->(q->F))->F))"),
               '-|': Formula.parse("(((p->(p->F))->((q->(q->F))->F))->F)"),
               '+': Formula.parse("((p->((p->(q->F))->F))->((q->((p->(q->F))->F))->F))"),
               '<->': Formula.parse("(((p->((p->(q->F))->F))->((q->((p->(q->F))->F))->F))->F)"),
               'T': Formula.parse("(p->p)")}
    return formula.substitute_operators(sub_map)
