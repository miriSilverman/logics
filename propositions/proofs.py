# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/proofs.py

"""Proofs by deduction in Propositional Logic."""

from __future__ import annotations
from typing import AbstractSet, FrozenSet, List, Mapping, Optional, Sequence, \
                   Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

from propositions.syntax import *

#: A mapping from variable names to formulas.
SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in Propositional Logic, comprised of zero
    or more assumed propositional formulas, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Sequence[Formula], conclusion: Formula):
        """Initializes an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return isinstance(other, InferenceRule) and \
               self.assumptions == other.assumptions and \
               self.conclusion == other.conclusion

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))
        
    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # Task 4.1
        vars = self.conclusion.variables()
        for assumption in self.assumptions:
            vars = vars.union(assumption.variables())
        return vars


    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """        
        for variable in specialization_map:
            assert is_variable(variable)
        # Task 4.4
        assumptions = [assumption.substitute_variables(specialization_map) for assumption in self.assumptions]
        conclusion = self.conclusion.substitute_variables(specialization_map)
        return InferenceRule(assumptions, conclusion)


    @staticmethod
    def _merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps while checking their
        consistency.

        Parameters:
            specialization_map1: first mapping to merge, or ``None``.
            specialization_map2: second mapping to merge, or ``None``.

        Returns:
            A single mapping containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)
        # Task 4.5a
        if specialization_map1 == None or specialization_map2 == None:
            return None

        map1 = dict(specialization_map1)
        map2 = dict(specialization_map2)
        map1.update(map2)
        map2.update(specialization_map1)

        if map1 ==  map2 :
            return map1
        else:
            return None


    @staticmethod
    def _formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # Task 4.5b
        specialization_map = {}
        if is_variable(general.root):
            cur_map = {general.root: specialization}
            return cur_map
        elif is_constant(general.root):
            if general.root == specialization.root:
                return specialization_map
            return None
        elif is_binary(general.root):
            if general.root != specialization.root:
                return None
            first_map = InferenceRule._formula_specialization_map(general.first, specialization.first)
            second_map = InferenceRule._formula_specialization_map(general.second, specialization.second)
            merged_map = InferenceRule._merge_specialization_maps(first_map, second_map)
            return InferenceRule._merge_specialization_maps(merged_map, specialization_map)
        elif is_unary(general.root):
            if general.root != specialization.root:
                return None
            map = InferenceRule._formula_specialization_map(general.first, specialization.first)
            return InferenceRule._merge_specialization_maps(map, specialization_map)




    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        # Task 4.5c
        if len(self.assumptions) != len(specialization.assumptions):
            return None
        specialization_map = {}
        if len(self.assumptions) > 0:
            for assumption_gen, assumption_spec in zip(self.assumptions, specialization.assumptions):
                map = InferenceRule._formula_specialization_map(assumption_gen, assumption_spec)
                specialization_map = InferenceRule._merge_specialization_maps(specialization_map, map)
                if specialization_map ==  None:
                    return None
        map = InferenceRule._formula_specialization_map(self.conclusion, specialization.conclusion)

        return InferenceRule._merge_specialization_maps(specialization_map, map)



    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

@frozen
class Proof:
    """An immutable deductive proof in Propositional Logic, comprised of a
    statement in the form of an inference rule, a set of inference rules that
    may be used in the proof, and a list of lines that prove the statement via
    these inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statement: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]
    
    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Sequence[Proof.Line]):
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula that
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule,
                out of those allowed in the proof, that has a specialization
                that concludes the formula; or ``None`` if the formula is
                justified as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): tuple of zero
                or more numbers of previous lines in the proof whose formulas
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Sequence[int]] = None):
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and numbers of justifying previous lines.

            Parameters:
                formula: the formula to be justified by the line.
                rule: the inference rule, out of those allowed in the proof,
                    that has a specialization that concludes the formula; or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
                assumptions: numbers of previous lines in the proof whose
                    formulas are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current line.

            Returns:
                A string representation of the current line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                r = str(self.formula) + '    (Inference Rule ' + str(self.rule)
                if len(self.assumptions) == 1:
                    r += ' on line ' + str(self.assumptions[0])
                elif len(self.assumptions) > 1:
                    r += ' on lines ' + ','.join(map(str, self.assumptions))
                r += ')'
                return r

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None
        
    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof of ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += 'Lines:\n'
        for i in range(len(self.lines)):
            r += ('%3d) ' % i) + str(self.lines[i]) + '\n'
        r += "QED\n"
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulas justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: number of the line according to which to compute the
                inference rule.

        Returns:
            The computed inference rule, with assumptions ordered in the order
            of their numbers in the specified line, or ``None`` if the specified
            line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        # Task 4.6a
        line = self.lines[line_number]
        line_rule = line.rule
        if line_rule == None:
            return None

        line_numbers = line.assumptions
        if len(line_numbers) != len(line_rule.assumptions):
            return
        assumptions = []
        for line_num in line_numbers:
            f = self.lines[line_num].formula
            assumptions.append(f)
        rule = InferenceRule(assumptions, line.formula)
        return rule


    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: number of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            ``True`` if the rule specified for that line is one of the allowed
            inference rules in the current proof, and it has a specialization
            that satisfies all of the following:

            1. The conclusion of that specialization is the formula justified by
               that line.
            2. The assumptions of this specialization are the formulas justified
               by the lines that are specified as the assumptions of that line
               (in the order of their numbers in that line), all of which must
               be previous lines.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        line = self.lines[line_number]

        if line.rule == None:       # the formula is an assumption
            if line.formula in self.statement.assumptions:
                return True
            return False

        if line.rule not in self.rules:     # rule not in the proofs rules
            return False

        for num in line.assumptions:        # based on lines that are after the current line
            if num >= line_number:
                return False

        rule = self.rule_for_line(line_number)      # the combined rule from the lines
        if rule == None:
            return False
        if rule.is_specialization_of(line.rule):
            return True
        return False


    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        num_of_lines = len(self.lines)
        if num_of_lines==0:
            return False
        for line in range(num_of_lines):
            if not self.is_line_valid(line):
                return False
        last_line = self.lines[num_of_lines-1]
        if last_line.formula == self.statement.conclusion:
            return True
        return False


# Chapter 5 tasks

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule to a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)
    # Task 5.1
    map = proof.statement.specialization_map(specialization)
    lines = [None]*len(proof.lines)
    for num, line in enumerate(proof.lines):
        formula = line.formula.substitute_variables(map)
        if line.rule == None:
            rule = None
            assumptions = None
        else:
            rule = line.rule
            assumptions = line.assumptions
        lines[num] = Proof.Line(formula, rule, assumptions)

    new_proof = Proof(specialization, proof.rules, lines)
    return new_proof




def _inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) \
    -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line_number: number of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating justification line numbers specified throughout the proof
        to maintain the validity of the proof. The set of allowed inference
        rules in the returned proof is the union of the rules allowed in the two
        given proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()
    # Task 5.2a
    len_of_lemma = len(lemma_proof.lines)
    cur_line = main_proof.lines[line_number]
    current_line_num = line_number
    lines_map = create_lines_map(len_of_lemma, line_number, main_proof) # {old_num: new_num}

    lines = [line for line in main_proof.lines[:line_number]]   # lines before line_number

    new_lemma_proof_for_cur_line = lemma_new_proof(cur_line, lemma_proof, main_proof)

    for proof_line in new_lemma_proof_for_cur_line.lines:   # lines of lemma
        new_line = correct_proof_line(current_line_num, lines, proof_line)
        lines.append(new_line)
    current_line_num += len_of_lemma

    for num, line in enumerate(main_proof.lines[line_number + 1:]):     # line after line_num
        if line.rule == None:
            new_line = Proof.Line(line.formula)
        else:
            new_line = Proof.Line(line.formula, line.rule, [lines_map[i] for i in line.assumptions])
        lines.append(new_line)
        current_line_num += 1

    new_lemma_proof_for_cur_line = Proof(main_proof.statement, main_proof.rules.union(lemma_proof.rules), lines)
    return new_lemma_proof_for_cur_line


def correct_proof_line(current_line_num, lines, proof_line):
    """
    :param current_line_num: the number of the last line in the proof before the lemma
    :param lines: the list of all the lines in the proof until the current one
    :param proof_line: the line in the lemma to adjust to the right numbers of lines
    :return: the line in the lemma with the right rules and assumptions
    """
    if proof_line.rule != None:
        new_line = Proof.Line(proof_line.formula, proof_line.rule,
                              [i + current_line_num for i in proof_line.assumptions])
    else:
        new_line = Proof.Line(proof_line.formula)

        for a_line in lines:  # case that the formula was in a prior line
            if a_line.formula == proof_line.formula:
                new_line = a_line
    return new_line


def lemma_new_proof(cur_line, lemma_proof, main_proof):
    """
    :param cur_line: the line in the proof where its rule is the lemma
    :param lemma_proof: the lemma proof
    :param main_proof: the main proof
    :return: specialization of the lemma for the current line
    """
    assumptions = [main_proof.lines[i].formula for i in cur_line.assumptions]
    rule = InferenceRule(assumptions, cur_line.formula)
    new_proof = prove_specialization(lemma_proof, rule)
    return new_proof


def create_lines_map(len_of_lemma, line_number, main_proof):
    """
    :param len_of_lemma: length of lemma
    :param line_number: line number of line with rule that is the lemma
    :param main_proof: main proof
    :return: map of the old number of line to the new number of line
    """
    lines_map = {}  # {old_num: new_num}
    i = 0
    while i < len(main_proof.lines):
        if i < line_number:
            lines_map[i] = i
        else:
            lines_map[i] = i + len_of_lemma - 1
        i += 1
    return lines_map


def inline_proof1(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    # Task 5.2b
    len_of_lemma = len(lemma_proof.lines)

    # taking out the lemma rule
    rules = set()
    for rule in main_proof.rules:
        if rule != lemma_proof.statement:
            rules.add(rule)
    rules = rules.union(lemma_proof.rules)


    i = 0
    while i < len(main_proof.lines):
        if main_proof.lines[i].rule == lemma_proof.statement:   # the rule of the line is the lemma
            main_proof = _inline_proof_once(main_proof, i, lemma_proof)
            i += len_of_lemma
        else:
            i += 1

    return Proof(main_proof.statement, rules, main_proof.lines)

def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.
    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.
    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the
        rules allowed in the two given proofs but without the "lemma" rule
        proved by `lemma_proof`.
    """
    # Task 5.2b
    lemma_as_a_rule = lemma_proof.statement
    lines = []
    current_line_num = 0
    len_of_lemma = len(lemma_proof.lines)
    lines_map = {}      # {old_num: new_num}
    for num, line in enumerate(main_proof.lines):
        if line.rule == lemma_as_a_rule:
            new_proof = lemma_new_proof(line, lemma_proof, main_proof)
            for proof_line in new_proof.lines:
                new_line = correct_proof_line(current_line_num, lines, proof_line)
                lines.append(new_line)
            current_line_num += len_of_lemma
            lines_map[num] = current_line_num - 1
        else:
            if line.rule == None:
                new_line =  Proof.Line(line.formula)
            else:
                new_line = Proof.Line(line.formula, line.rule, [lines_map[i] for i in line.assumptions])
            lines.append(new_line)
            lines_map[num] = current_line_num
            current_line_num += 1

    rules = set()
    for rule in main_proof.rules:
        if rule != lemma_as_a_rule:
            rules.add(rule)
    rules = rules.union(lemma_proof.rules)

    new_proof = Proof(main_proof.statement, rules, lines)
    return new_proof