# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/syntax.py

"""Syntactic handling of predicate-logic expressions."""

from __future__ import annotations
import re

from functools import lru_cache
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen, \
                        memoized_parameterless_method

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context.

    Attributes:
        variable_name (`str`): the variable name that was forbidden in the
            context in which a term containing it was to be substituted.
    """
    variable_name: str

    def __init__(self, variable_name: str):
        """Initializes a `ForbiddenVariableError` from the offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it is to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

@lru_cache(maxsize=100) # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((string[0] >= '0' and string[0] <= '9') or \
              (string[0] >= 'a' and string[0] <= 'd')) and \
             string.isalnum()) or string == '_'

@lru_cache(maxsize=100) # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return string[0] >= 'u' and string[0] <= 'z' and string.isalnum()

@lru_cache(maxsize=100) # Cache the return value of is_function
def is_function(string: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return string[0] >= 'f' and string[0] <= 't' and string.isalnum()

@frozen
class Term:
    """An immutable predicate-logic term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str, arguments: Optional[Sequence[Term]] = None):
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        elif is_function(self.root):
            return self.repr_parameters()


    def repr_parameters(self):
        s = self.root + "("
        for num, arg in enumerate(self.arguments):
            s += str(arg)
            if num < len(self.arguments) - 1:
                s += ","
        s += ")"
        return s

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1
        if is_variable(string[0]):
            var = re.compile("(.[a-zA-Z0-9]*)(.*)")
            m = var.match(string)
            return Term(m.group(1)), m.group(2)

        elif is_constant(string[0]):
            if string[0] == '_':
                return Term('_'), string[1:]
            var = re.compile("([\d\w]*)(.*)")
            m = var.match(string)
            return Term(m.group(1)), m.group(2)


        elif is_function(string[0]):
            args = []
            func = re.compile("([^(]*)\(([^)^,^(].*)\).*")
            m = func.match(string)
            if m:
                func_name = m.group(1)
                start_func_body_idx = m.start(2)

                if (not is_function(func_name)):    # the part before the parenthesis is not a valid func name
                    return None, string

                # parsing the content of the function (including the parenthesis and the rest)
                term, rest = Term._parse_prefix(string[start_func_body_idx:])
                args.append(term)

                # case of no closing parenthesis or illegal pattern
                if len(rest) == 0 or (rest[0] not in {',', ')'}):
                    return None, string


                while rest[0] == ',':
                    term, rest = Term._parse_prefix(rest[1:])
                    if term == None:        # case of no arg after comma
                        return None, string
                    args.append(term)

                if rest[0] == ')':
                    rest = rest[1:] if len(rest) > 1 else ''
                    return Term(func_name, tuple(args)), rest


            else:   # the string doesnt is not in the right format of a function
                return None, string

        else:   # string[0] is a char that doesnt correspond to any pattern
            return None, string





    @staticmethod
    def parse(string: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            string: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2
        return Term._parse_prefix(string)[0]


    def extraction_helper(self, set: Set[str], task, vars: Set = None):
        if is_constant(self.root) and task == 1:
            set.add(self.root)
        elif is_variable(self.root):
            if task == 2:
                set.add(self.root)
            elif task == 4:
                if self.root not in vars:
                    set.add(self.root)
        elif is_function(self.root):
            if task == 3:
                set.add((self.root, len(self.arguments)))
            for arg in self.arguments:
                arg.extraction_helper(set, task, vars)





    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        # Task 7.5.1
        consts = set()
        self.extraction_helper(consts, 1)
        return consts





    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        # Task 7.5.2
        vars = set()
        self.extraction_helper(vars, 2)
        return vars


    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        # Task 7.5.3
        funcs = set()
        self.extraction_helper(funcs, 3)
        return funcs


    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))

            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

@lru_cache(maxsize=100) # Cache the return value of is_equality
def is_equality(string: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return string == '='

@lru_cache(maxsize=100) # Cache the return value of is_relation
def is_relation(string: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return string[0] >= 'F' and string[0] <= 'T' and string.isalnum()

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
    return string == '&' or string == '|' or string == '->'

@lru_cache(maxsize=100) # Cache the return value of is_quantifier
def is_quantifier(string: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return string == 'A' or string == 'E'

@frozen
class Formula:
    """An immutable predicate-logic formula in tree representation, composed
    from relation names applied to predicate-logic terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None):
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the root, if the
                root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2
        if is_unary(self.root):
            return '~' + str(self.first)
        elif is_binary(self.root):
            return "("+str(self.first)+self.root+str(self.second)+")"
        elif is_relation(self.root):
            return self.repr_parameters()
        elif is_quantifier(self.root):
            return self.root + self.variable + '[' + str(self.predicate) + ']'
        elif is_equality(self.root):
            return str(self.arguments[0]) + '=' + str(self.arguments[1])

    def repr_parameters(self):
        s = self.root + "("
        for num, arg in enumerate(self.arguments):
            s += str(arg)
            if num < len(self.arguments) - 1:
                s += ","
        s += ")"
        return s


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


    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1
        first_char = string[0]

        if is_unary(first_char):
            if len(string) < 2:
                return None, string

            formula, rest = Formula._parse_prefix(string[1:])
            if formula == None:
                return None, string
            return Formula('~', formula), rest

        elif first_char == '(':     # binary case
            first_formula, rest = Formula._parse_prefix(string[1:])

            # cases of missing operator or a one of the args
            if first_formula == None or len(rest) < 3:
                return None, string

            if not is_binary(rest[0]):
                operator = rest[0:2]
                second_formula_idx = 2
                if not is_binary(operator):
                    return None, string
            else:
                operator = rest[0]
                second_formula_idx = 1

            second_formula, rest = Formula._parse_prefix(rest[second_formula_idx:])

            # case of missing second arg or missing closing parenthesis
            if second_formula == None or len(rest) < 1 or rest[0] != ')':
                return None, string

            return Formula(operator, first_formula, second_formula), rest[1:]


        elif first_char <='T' and first_char >= 'F':     # relation case
            relation = re.compile("([^(]*)\((.*)\)(.*)")
            m = relation.match(string)
            if m:
                relation_name = m.group(1)
                if not is_relation(relation_name):
                    return None, string
                relation_body_start_idx = m.start(2)

                args = []
                arg, rest = Term._parse_prefix(string[relation_body_start_idx:])
                if arg == None and rest[0] == ')':
                    rest = rest[1:] if len(rest) > 1 else ''
                    return Formula(relation_name, args), rest

                if arg == None or len(rest) < 1 or rest[0] not in {',', ')'}:
                    return None, string
                args.append(arg)

                while rest[0] == ',':
                    if len(rest) < 3:   # no arg after comma or missing closing parenthesis
                        return None, string
                    arg, rest = Term._parse_prefix(rest[1:])
                    if arg == None or len(rest) < 1:        # no arg after comma or missing closing parenthesis
                        return None, string
                    args.append(arg)

                if rest[0] == ')':
                    rest = rest[1:] if len(rest) > 1 else ''
                    return Formula(relation_name, args), rest

            else:   # no open parenthesis case
                return None, string

        elif is_quantifier(first_char):     # quantifier case
            if len(string) < 5:
                return None, string
            quantifier = re.compile("([^\[]+)\[(.+)\](.*)")
            m = quantifier.match(string[1:])
            if m:
                var_name = m.group(1)
                if not is_variable(var_name):   # var name is not in the right format
                    return None, string

                quantifier_body_start_idx = m.start(2) + 1
                formula, rest = Formula._parse_prefix(string[quantifier_body_start_idx:])

                if formula == None or len(rest) < 1 or rest[0] != ']':
                    return None, string

                rest = rest[1:] if len(rest) > 1 else ''
                return Formula(first_char, var_name, formula), rest

            else:       # not the right pattern of  quantifier
                return None, string


        elif is_variable(first_char) or is_constant(first_char) or is_function(first_char):   # equality case

            first_term, rest = Term._parse_prefix(string)
            if first_term == None or len(rest) < 2 or rest[0] != '=':
                return None, string

            second_term, rest = Term._parse_prefix(rest[1:])
            if second_term == None:
                return None, string

            f = Formula('=', (first_term, second_term)), rest
            # print("f ", f)
            return f


        else:
            return None, string



    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        return Formula._parse_prefix(string)[0]


    def form_extract_helper(self, set: Set, task, vars: Set = None):
        if is_unary(self.root):
            self.first.form_extract_helper(set, task, vars)
        elif is_binary(self.root):
            copy_of_vars = None if vars == None else vars.copy()
            self.first.form_extract_helper(set, task, vars)
            self.second.form_extract_helper(set, task, copy_of_vars)
        elif is_relation(self.root):
            if task == 5:
                set.add((self.root, len(self.arguments)))
            for term in self.arguments:
                term.extraction_helper(set, task, vars)
        elif is_equality(self.root):
            for term in self.arguments:
                term.extraction_helper(set, task, vars)
        elif is_quantifier(self.root):
            if task == 2:
                set.add(self.variable)
            elif task == 4:
                vars.add(self.variable)
            self.predicate.form_extract_helper(set, task, vars)


    @memoized_parameterless_method
    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        # Task 7.6.1
        const = set()
        self.form_extract_helper(const, 1)
        return const



    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 7.6.2
        vars = set()
        self.form_extract_helper(vars, 2)
        return vars

    @memoized_parameterless_method
    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of every variable name that is used in the current formula not
            only within a scope of a quantification on that variable name.
        """
        # Task 7.6.3
        vars = set()
        free_vars = set()
        self.form_extract_helper(free_vars, 4, vars)
        return free_vars


    @memoized_parameterless_method
    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        # Task 7.6.4
        funcs = set()
        self.form_extract_helper(funcs, 3)
        return funcs


    @memoized_parameterless_method
    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        # Task 7.6.5
        relations = set()
        self.form_extract_helper(relations, 5)
        return relations

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map`\ ``[``\ `name`\ ``]``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z

            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a mapping from each atomic
            propositional formula to the subformula for which it was
            substituted.

        Examples:
            >>> formula = Formula.parse('((Ax[x=7]&x=7)|(x=7->~Q(y)))')
            >>> formula.propositional_skeleton()
            (((z1&z2)|(z2->~z3)), {'z1': Ax[x=7], 'z2': x=7, 'z3': Q(y)})
            >>> formula.propositional_skeleton()
            (((z4&z5)|(z5->~z6)), {'z4': Ax[x=7], 'z5': x=7, 'z6': Q(y)})
        """
        # Task 9.8

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a predicate-logic formula from a propositional skeleton and
        a substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute,
                containing no constants or operators beyond ``'~'``, ``'->'``,
                ``'|'``, and ``'&'``.
            substitution_map: mapping from each atomic propositional subformula
                of the given skeleton to a predicate-logic formula.

        Returns:
            A predicate-logic formula obtained from the given propositional
            skeleton by substituting each atomic propositional subformula with
            the formula mapped to it by the given map.

        Examples:
            >>> Formula.from_propositional_skeleton(
            ...     PropositionalFormula.parse('((z1&z2)|(z2->~z3))'),
            ...     {'z1': Formula.parse('Ax[x=7]'), 'z2': Formula.parse('x=7'),
            ...      'z3': Formula.parse('Q(y)')})
            ((Ax[x=7]&x=7)|(x=7->~Q(y)))
        """
        for operator in skeleton.operators():
            assert is_unary(operator) or is_binary(operator)
        for variable in skeleton.variables():
            assert variable in substitution_map
        # Task 9.10
