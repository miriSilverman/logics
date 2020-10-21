# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union
import re

from logic_utils import frozen, memoized_parameterless_method

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdigit())

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100) # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == '~'

@lru_cache(maxsize=100) # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    return string in {'&', '|',  '->', '+', '<->', '-&', '-|'}

@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    atomic propositions, and operators applied to them.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        if is_variable(self.root):
            return self.root
        elif is_constant(self.root):
            return self.root
        elif is_unary(self.root):
            return self.root + str(self.first)
        elif is_binary(self.root):
            return "(" + str(self.first) + self.root + str(self.second)+")"


    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        var_set = set()
        self.form_helper(self, 2, var_set)
        return var_set



    def form_helper(self, formula, task, t_set):
        """
        Args:
            formula: the formula
            task: finding operators or variables
            t_set: set of variables or operators
        """
        if is_variable(formula.root):
            if task == 2:
                t_set.add(formula.root)
        elif is_constant(formula.root):
            if task == 3:
                t_set.add(formula.root)
        elif is_unary(formula.root):
            if task == 3:
                t_set.add(formula.root)
            self.form_helper(formula.first, task, t_set)
        elif is_binary(formula.root):
            if task == 3:
                t_set.add(formula.root)
            self.form_helper(formula.first, task, t_set)
            self.form_helper(formula.second, task, t_set)


    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        op_set = set()
        self.form_helper(self, 3, op_set)
        return op_set



    @staticmethod
    def parse_prefix_helper(string: str):
        """
        Args:
            string: string to parse
        Returns: Tuple of array consisting the formula first, root anf second and the rest of the string
        """
        par_counter = 0     # indicates the balance between open and close parenthesis
        formula_partition = None    # first, root, second
        operator_indx = 0           # the index of the binary operation
        i = 0
        while i < len(string):
            if string[i] == "(":
                par_counter += 1
            elif string[i] == ")":
                par_counter -= 1

            if par_counter == 1:
                if string[i] in {'&', '|', '+'}:
                    operator_indx = i
                    formula_partition = [string[1:i], string[i], string[i + 1:-1]]
                elif string[i] == '<':
                    if i+1 < len(string) and string[i+1] == '-' and string[i+2]=='>':
                        operator_indx = i+2
                        formula_partition = [string[1:i], "<->", string[i + 2:-1]]
                        i+=2
                elif string[i] == "-":
                    if i < len(string) and string[i+1] == ">":
                        operator_indx = i+1
                        formula_partition = [string[1:i], "->", string[i + 1:-1]]
                    elif i < len(string) and string[i+1] == "&":
                        operator_indx = i+1
                        formula_partition = [string[1:i], "-&", string[i + 1:-1]]
                        i+=1
                    elif i < len(string) and string[i+1] == "|":
                        operator_indx = i+1
                        formula_partition = [string[1:i], "-|", string[i + 1:-1]]
                        i+=1
                    else:
                        return formula_partition, None


            if par_counter == 0 and formula_partition != None:      # got to the closing parenthesis
                formula_partition[2] = string[operator_indx + 1:i]  # second son to be until the closing parenthesis
                return formula_partition, string[i + 1:]            # adding the rest
            i += 1
        return formula_partition, None


    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator follows by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        is_var = re.compile("([p-z][0-9]*)").match(string)

        if len(string) == 0:        # empty string
            return None, 'ERROR: empty string'
        if is_constant(string[0]):      # constant
            return Formula(string[0]), string[1:]
        if is_var:                      # variable
            variable = is_var.group(1)
            return Formula(variable), string[len(variable):]
        if is_unary(string[0]):         # unary operation
            if len(string) == 1:
                return None, 'ERROR: missing literal after unary operator'
            formula_partition, rest = Formula._parse_prefix(string[1:])
            return Formula(string[0], formula_partition), rest
        if string[0] == '(':            # binary operation
            partition, rest = Formula.parse_prefix_helper(string)
            if partition is None or rest is None:
                return None, 'ERROR: binary section not correct'

            first, rest1 = Formula._parse_prefix(partition[0])
            second, rest2 = Formula._parse_prefix(partition[2])

            if rest1 == rest2 == '' and not None in {first, second}:
                return Formula(partition[1], first, second), rest

        return None, 'ERROR: illegal character'




    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        formula, extra = Formula._parse_prefix(string)
        return formula != None and extra == ''




        
    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6
        return Formula._parse_prefix(string)[0]


# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7
        if is_binary(self.root):
            return self.root + self.first.polish() + self.second.polish()
        elif is_unary(self.root):
            return self.root + self.first.polish()
        elif is_variable(self.root):
            return self.root
        elif is_constant(self.root):
            return self.root




    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8
        # if is_constant(string):
        #     return Formula(string)
        # elif is_variable(string):
        #     return Formula(string)
        # elif is_unary(string[0]):
        #     return Formula(string[0], Formula.parse_polish(string[1:]))
        # elif string[0] in {'&', '|'}:
        #     is_var = re.compile("^([p-z][0-9]*)+").match(string[1:])
        #     if is_var: #  &xy || &x|xy
        #         first = is_var.group(1)
        #         return Formula(string[0], Formula.parse_polish(first), Formula.parse_polish(string[len(first) + 1:]))
        #     elif is_constant(string[1]):
        #         return Formula(string[0], Formula.parse_polish(string[1]), Formula.parse_polish(string[2:]))
        #     elif is_unary(string[1]):









    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
        Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variables originating in the current formula are substituted (i.e.,
            variables originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        new_formula = Formula(self.root, self.first, self.second)
        new_formula.substitute_variables_helper(substitution_map)
        return new_formula

    def substitute_variables_helper(self, substitution_map: Mapping[str, Formula]):
        if is_variable(self.root):
            if self.root in substitution_map:
                f = substitution_map[self.root]
                self.root = f.root
                self.first = f.first
                self.second = f.second
        elif is_unary(self.root):
            self.first.substitute_variables_helper(substitution_map)
        elif is_binary(self.root):
            self.first.substitute_variables_helper(substitution_map)
            self.second.substitute_variables_helper(substitution_map)


if __name__ == '__main__':
    f = Formula.parse('((p->p)|r)').substitute_variables({'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
    print(f)


    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> \
        Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operators originating in the current formula are substituted (i.e.,
            operators originating in one of the specified substitutions are not
            subjected to additional substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
