# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/prover.py

"""Axiomatic schemas of Predicate Logic, and useful proof creation maneuvers
using them."""

from typing import AbstractSet, Collection, FrozenSet, List, Mapping, \
                   Sequence, Tuple, Union

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *

class Prover:
    """A class for gradually creating a predicate-logic proof from given
    assumptions as well as from the six axioms (`AXIOMS`) Universal
    Instantiation (`UI`), Existential Introduction (`EI`), Universal
    Simplification (`US`), Existential Simplification (`ES`), Reflexivity
    (`RX`), and Meaning of Equality (`ME`).

    Attributes:
        _assumptions (`~typing.FrozenSet`\\[`~predicates.proofs.Schema`]): the
            assumptions/axioms of the proof being created, which include
            `AXIOMS`.
        _lines (`~typing.List`\\[`~predicates.proofs.Proof.Line`]): the current
            lines of the proof being created.
        _print_as_proof_forms (`bool`): flag specifying whether the proof being
            created is being printed in real time as it forms.
    """
    _assumptions: FrozenSet[Schema]
    _lines: List[Proof.Line]
    _print_as_proof_forms: bool

    #: Axiom schema of universal instantiation
    UI = Schema(Formula.parse('(Ax[R(x)]->R(c))'), {'R', 'x', 'c'})
    #: Axiom schema of existential introduction
    EI = Schema(Formula.parse('(R(c)->Ex[R(x)])'), {'R', 'x', 'c'})
    #: Axiom schema of universal simplification
    US = Schema(Formula.parse('(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))'),
                {'Q', 'R', 'x'})
    #: Axiom schema of existential simplification
    ES = Schema(Formula.parse('((Ax[(R(x)->Q())]&Ex[R(x)])->Q())'),
                {'Q', 'R', 'x'})
    #: Axiom schema of reflexivity
    RX = Schema(Formula.parse('c=c'), {'c'})
    #: Axiom schema of meaning of equality
    ME = Schema(Formula.parse('(c=d->(R(c)->R(d)))'), {'R', 'c', 'd'})
    #: Axiomatic system for Predicate Logic, consisting of `UI`, `EI`, `US`,
    #: `ES`, `RX`, and `ME`.
    AXIOMS = frozenset({UI, EI, US, ES, RX, ME})

    def __init__(self, assumptions: Collection[Union[Schema, Formula, str]],
                 print_as_proof_forms: bool=False):
        """Initializes a `Prover` from its assumptions/additional axioms. The
        proof created by the prover initially has no lines.

        Parameters:
            assumptions: the assumptions/axioms beyond `AXIOMS` for the proof
                to be created, each specified as either a schema, a formula that
                constitutes the unique instance of the assumption, or the string
                representation of the unique instance of the assumption.
            print_as_proof_forms: flag specifying whether the proof is to be
                printed in real time as it forms.
        """
        self._assumptions = \
            Prover.AXIOMS.union(
                {assumption if isinstance(assumption, Schema)
                 else Schema(assumption) if isinstance(assumption, Formula)
                 else Schema(Formula.parse(assumption))
                 for assumption in assumptions})
        self._lines = []
        self._print_as_proof_forms = print_as_proof_forms
        if self._print_as_proof_forms:
            print('Proving from assumptions/axioms:\n'
                  '  AXIOMS')
            for assumption in self._assumptions - Prover.AXIOMS:
                  print('  ' + str(assumption))
            print('Lines:')

    def qed(self) -> Proof:
        """Concludes the proof created by the current prover.

        Returns:
            A valid proof, from the assumptions of the current prover as well as
            `AXIOMS`', of the formula justified by the last line appended to the
            current prover.
        """
        conclusion = self._lines[-1].formula
        if self._print_as_proof_forms:
            print('Conclusion:', str(conclusion) + '. QED\n')
        return Proof(self._assumptions, conclusion, self._lines)

    def _add_line(self, line: Proof.Line) -> int:
        """Appends to the proof being created by the current prover the given
        validly justified line.

        Parameters:
            line: proof line that is validly justified when appended to the
                lines of the proof being created by the current prover.

        Returns:
            The line number of the appended line in the proof being created by
            the current prover.
        """
        line_number = len(self._lines)
        self._lines.append(line)
        assert line.is_valid(self._assumptions, self._lines, line_number)
        if self._print_as_proof_forms:
            print(('%3d) ' % line_number) + str(line.formula))
        return line_number

    def add_instantiated_assumption(self, instance: Union[Formula, str],
                                    assumption: Schema,
                                    instantiation_map: InstantiationMap) -> \
            int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given instance of the given assumptions/axioms of
        the current prover.

        Parameters:
            instance: instance to be appended, specified as either a formula or
                its string representation.
            assumption: assumption/axiom of the current prover that instantiates
                the given instance.
            instantiation_map: mapping instantiating the given instance from the
                given assumption/axiom. Each value of this map may also be given
                as a string representation (instead of a term or a formula).

        Returns:
            The line number of the newly appended line that justifies the given
            instance in the proof being created by the current prover.
        """
        if isinstance(instance, str):
            instance = Formula.parse(instance)
        instantiation_map = dict(instantiation_map)
        for key in instantiation_map:
            value = instantiation_map[key]
            if is_variable(key):
                assert is_variable(value)
            elif is_constant(key):
                if isinstance(value, str):
                    instantiation_map[key] = Term.parse(value)
                else:
                    assert isinstance(value, Term)
            else:
                assert is_relation(key)
                if isinstance(value, str):
                    instantiation_map[key] = Formula.parse(value)
                else:
                    assert isinstance(value, Formula)
        return self._add_line(Proof.AssumptionLine(instance, assumption,
                                                   instantiation_map))
        
    def add_assumption(self, unique_instance: Union[Formula, str]) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the unique instance of one of the assumptions/axioms
        of the current prover.

        Parameters:
            unique_instance: unique instance of one of the assumptions/axioms
                of the current prover, to be appended, specified as either a
                formula or its string representation.

        Returns:
            The line number of the newly appended line that justifies the given
            instance in the proof being created by the current prover.
        """
        if isinstance(unique_instance, str):
            unique_instance = Formula.parse(unique_instance)
        return self.add_instantiated_assumption(unique_instance,
                                                Schema(unique_instance), {})

    def add_tautology(self, tautology: Union[Formula, str]) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given tautology.

        Parameters:
            tautology: tautology to be appended, specified as either a formula
                or its string representation.

        Returns:
            The line number of the newly appended line that justifies the given
            tautology in the proof being created by the current prover.
        """
        if isinstance(tautology, str):
            tautology = Formula.parse(tautology)
        return self._add_line(Proof.TautologyLine(tautology))

    def add_mp(self, consequent: Union[Formula, str],
               antecedent_line_number: int, conditional_line_number: int) -> \
            int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given consequent of an MP inference from the
        specified already existing lines of the proof.

        Parameters:
            consequent: consequent of MP inference to be appended, specified as
                either a formula or its string representation.
            antecedent_line_number: line number in the proof of the antecedent
                of the MP inference that derives the given formula.
            conditional_line_number: line number in the proof of the conditional
                of the MP inference that derives the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(consequent, str):
            consequent = Formula.parse(consequent)
        return self._add_line(Proof.MPLine(consequent, antecedent_line_number,
                                           conditional_line_number))

    def add_ug(self, quantified: Union[Formula, str],
               unquantified_line_number: int) -> int:
        """Appends to the proof being created by the current prover a line that
        validly justifies the given universally quantified formula, whose
        predicate is the specified already existing line of the proof.

        Parameters:
            quantified: universally quantified formula to be appended, specified
                as either a formula or its string representation.
            unquantified_line_number: line number in the proof of the predicate
                of the given quantified formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(quantified, str):
            quantified = Formula.parse(quantified)
        return self._add_line(Proof.UGLine(quantified,
                                           unquantified_line_number))

    def add_proof(self, conclusion: Union[Formula, str], proof: Proof) -> int:
        """Appends to the proof being created by the current prover a validly
        justified inlined version of the given proof of the given conclusion,
        the last line of which validly justifies the given formula.

        Parameters:
            conclusion: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            proof: valid proof of the given formula from a subset of the
                assumptions/axioms of the current prover.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(conclusion, str):
            conclusion = Formula.parse(conclusion)
        assert proof.conclusion == conclusion
        assert proof.assumptions.issubset(self._assumptions)
        line_shift = len(self._lines)
        for line in proof.lines:
            if type(line) in {Proof.AssumptionLine, Proof.TautologyLine}:
                self._add_line(line)
            elif isinstance(line, Proof.MPLine):
                self.add_mp(line.formula,
                            line.antecedent_line_number + line_shift,
                            line.conditional_line_number + line_shift)
            else:
                assert isinstance(line, Proof.UGLine)
                self.add_ug(line.formula,
                            line.predicate_line_number + line_shift)
        line_number = len(self._lines) - 1
        assert self._lines[line_number].formula == conclusion
        return line_number                

    def add_universal_instantiation(self, instantiation: Union[Formula, str],
                                    line_number: int, term: Union[Term, str]) \
            -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the result of substituting a term for the
        outermost universally quantified variable name of the formula of the
        specified already existing line of the proof.

        Parameters:
            instantiation: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of a universally quantified
                formula of the form ``'A``\ `x`\ ``[``\ `predicate`\ ``]'``.
            term: term, specified as either a term or its string representation,
                that when substituted into the free occurrences of `x` in
                `predicate` yields the given formula.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula
            ``'Ay[Az[f(x,y)=g(z,y)]]'`` and `term` is ``'h(w)'``, then
            `instantiation` should be ``'Az[f(x,h(w))=g(z,h(w))]'``.
        """
        if isinstance(instantiation, str):
            instantiation = Formula.parse(instantiation)
        assert line_number < len(self._lines)
        quantified = self._lines[line_number].formula
        assert quantified.root == 'A'
        if isinstance(term, str):
            term = Term.parse(term)
        assert instantiation == \
               quantified.predicate.substitute({quantified.variable: term})
        # Task 10.1
        r = quantified.predicate.substitute({quantified.variable : Term('_')})  # (Man(_)->Mortal(_))
        f = Formula('->', quantified, instantiation)  # (Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))
        ui_line_num = self.add_instantiated_assumption(f, Prover.UI, {'R': r, 'c' :term, 'x': quantified.variable})
        return self.add_mp(instantiation, line_number, ui_line_num)



    def add_tautological_implication(self, implication: Union[Formula, str],
                                     line_numbers: AbstractSet[int]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the conclusion of a tautological inference whose
        assumptions are the specified already existing lines of the proof.

        Parameters:
            implication: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_numbers: line numbers in the proof of formulas from which
                conclusion can be a tautologically inferred.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(implication, str):
            implication = Formula.parse(implication)
        for line_number in line_numbers:
            assert line_number < len(self._lines)
        # Task 10.2
        # assumptions = []
        # all_map = {}
        # for num in line_numbers:
        #     line_formula = self._lines[num].formula
        #     prop_formula, map = line_formula.propositional_skeleton()
        #     for key in map:
        #         if key not in all_map:
        #             all_map[key] = map[key]
        #     f = Prover.update_formula(prop_formula, map, all_map)
        #     assumptions.append(f)
        #
        #     print(f)
        # conclusion, map = implication.propositional_skeleton()
        # conclusion = Prover.update_formula(conclusion, map, all_map)
        # print(conclusion)
        # rule = PropositionalInferenceRule(assumptions, conclusion)
        # print(rule)
        #
        # proof = prove_sound_inference(rule)
        line_nums = list(line_numbers)
        tautology = self.concat_imply(implication, line_nums, 0)
        tautology_line_num = self.add_tautology(tautology)
        self.concat_mp(line_nums, tautology, 0, tautology_line_num)
        return tautology_line_num+len(line_nums)



    def concat_imply(self, implication: Union[Formula, str], line_numbers: list, idx) -> Formula:
        """
        Args:
            implication: conclusion to prove
            line_numbers: numbers of line to concatenate their formulas with ->
            idx: current index in the concatenation

        Returns: formula of format: x1->x2->...->xn->implication
        where xi is the formula of corresponding line_number
        """
        if idx == len(line_numbers):
            return implication
        return Formula('->', self._lines[line_numbers[idx]].formula, self.concat_imply(implication, line_numbers, idx+1))




    def concat_mp(self, line_numbers: list, tautology: Formula, idx, last_line_num: int):
        """
        "unfolds" the tautology of format: x1->x2->x3->...->xn->conclusion, all the way to conclusion,
        with MP
        Args:
            tautology: tautology of format: x1->x2->x3->...->xn->conclusion
            line_numbers: numbers of lines that put together the tautology [line_of_x1, line_of_x2,.., line_of_xn]
            idx: current index of the p in "p , p->q, ---> q"
            last_line_num: number of the last line in the proof
        """
        if idx == len(line_numbers):
            return
        self.add_mp(tautology.second, line_numbers[idx], last_line_num)
        self.concat_mp(line_numbers, tautology.second, idx+1, last_line_num+1)



    # def update_formula(formula: PropositionalFormula, cur_map, all_map):
    #     root = formula.root
    #     if is_unary(root):
    #         return PropositionalFormula(root, Prover.update_formula(formula.first, cur_map, all_map))
    #     elif is_binary(root):
    #         first = Prover.update_formula(formula.first, cur_map, all_map)
    #         second = Prover.update_formula(formula.second, cur_map, all_map)
    #         return PropositionalFormula(root, first, second)
    #     elif is_variable(root) or is_constant(root):
    #         for key in all_map:
    #             if cur_map[root] == all_map[key]:
    #                 return PropositionalFormula(key)



    def add_existential_derivation(self, consequent: Union[Formula, str],
                                   line_number1: int, line_number2: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the consequent of the second specified already
        existing line of the proof, whose antecedent is existentially quantified
        in the first specified already existing line of the proof.

        Parameters:
            consequent: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number1: line number in the proof of an existentially
                quantified formula of the form
                ``'E``\ `x`\ ``[``\ `antecedent(x)`\ ``]'``, where `x`
                is a variable name that may have free occurrences in
                `antecedent(x)` but has no free occurrences in `consequent`.
            line_number2: line number in the proof of the formula
                ``'(``\ `antecedent(x)`\\ ``->``\ `consequent`\ ``)'``.

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
        """
        if isinstance(consequent, str):
            consequent = Formula.parse(consequent)
        assert line_number1 < len(self._lines)
        quantified = self._lines[line_number1].formula
        assert quantified.root == 'E'
        assert quantified.variable not in consequent.free_variables()
        assert line_number2 < len(self._lines)
        conditional = self._lines[line_number2].formula
        assert conditional == Formula('->', quantified.predicate, consequent)
        # Task 10.3
        x = quantified.variable
        line_1_formula = self._lines[line_number1].formula          # Ex[Man(x)]
        line_2_formula = self._lines[line_number2].formula          # (Man(x)->Ex[Mortal(x)])
        f = Formula('A', x, line_2_formula)     # Ax[(Man(x)->Ex[Mortal(x)])]
        and_formula = Formula('&', f, line_1_formula)  # (Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])
        imply_formula = Formula('->', and_formula, consequent)      # ((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])


        line_ug = self.add_ug(f, line_number2)
        r = line_1_formula.predicate.substitute({x: Term('_')}, set())  # Man(_)
        es_line_num = self.add_instantiated_assumption(imply_formula, Prover.ES, {'Q': consequent, 'R': r, 'x': x})
        return self.add_tautological_implication(consequent, {line_number1, line_ug, es_line_num})



    def add_flipped_equality(self, flipped: Union[Formula, str],
                             line_number: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, which is the result of exchanging the two sides of an
        equality from the specified already existing line of the proof.

        Parameters:
            flipped: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of an equality that is the
                same as the given equality, except that the two sides of the
                equality are exchanged.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.
        """
        if isinstance(flipped, str):
            flipped = Formula.parse(flipped)
        assert is_equality(flipped.root)
        assert line_number < len(self._lines)
        equality = self._lines[line_number].formula
        assert equality == Formula('=', [flipped.arguments[1],
                                         flipped.arguments[0]])
        # Task 10.6
        c = flipped.arguments[1]
        d = flipped.arguments[0]
        c_c= Formula('=', [c,c])
        c_d = Formula('=', [c,d])
        d_c = Formula('=', [d,c])
        l1 = self.add_instantiated_assumption(c_c, Prover.RX, {'c':c})
        f1 = Formula('->', c_c, d_c)
        f2 = Formula('->', c_d, f1)
        l2 = self.add_instantiated_assumption(f2, Prover.ME, {'R': Formula('=',[Term('_'),c]),'c':c, 'd':d})
        l3 = self.add_mp(f1, line_number, l2)
        l4 = self.add_mp(f1.second, l1, l3)
        return l4





    def add_free_instantiation(self, instantiation: Union[Formula, str],
                               line_number: int,
                               substitution_map:
                               Mapping[str, Union[Term, str]]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given formula, which is the result of substituting terms for the free
        variable names of the formula of the specified already existing line of
        the proof.

        Parameters:
            instantiation: conclusion of the sequence of lines to be appended,
                which contains no variable names starting with ``z``, specified
                as either a formula or its string representation.
            line_number: line number in the proof of a formula with free
                variables, which contains no variable names starting with ``z``.
            substitution_map: mapping from free variable names of the formula
                with the given line number to terms that contain no variable
                names starting with ``z``, to be substituted for them to obtain
                the given formula. Each value of this map may also be given as a
                string representation (instead of a term). Only variable names
                originating in the formula with the given line number are
                substituted (i.e., variable names originating in one of the
                specified substitutions are not subjected to additional
                substitutions).

        Returns:
            The line number of the newly appended line that justifies the given
            formula in the proof being created by the current prover.
            
        Examples:
            If Line `line_number` contains the formula
            ``'(z=5&Az[f(x,y)=g(z,y)])'`` and `substitution_map` is
            ``{'y': 'h(w)', 'z': 'y'}``, then `instantiation` should be
            ``'(y=5&Az[f(x,h(w))=g(z,h(w))])'``.
        """
        if isinstance(instantiation, str):
            instantiation = Formula.parse(instantiation)
        assert line_number < len(self._lines)
        substitution_map = dict(substitution_map)
        for variable in substitution_map:
            assert is_variable(variable)
            term = substitution_map[variable]
            if isinstance(term, str):
                substitution_map[variable] = term = Term.parse(term)
            for variable in term.variables():
                assert variable[0] != 'z'
        assert instantiation == \
               self._lines[line_number].formula.substitute(substitution_map)
        for variable in instantiation.variables():
            assert variable[0] != 'z'
        # Task 10.7
        prev_line = self._lines[line_number]
        formula = prev_line.formula
        vars = formula.variables()      # 0=plus(minus(x),x)
        temp_conversion = dict()        # {zi: substitution_map[vi]}
        last_line = line_number
        for v in vars:  # 0=plus(minus(z55),z55)
            l = self.add_ug(Formula('A', v, formula), last_line)
            temp_var = next(fresh_variable_name_generator)
            temp_conversion[temp_var] = substitution_map[v]
            formula = formula.substitute({v:Term(temp_var)})
            last_line = self.add_universal_instantiation(formula, l, temp_var)


        temp_formula = self._lines[last_line].formula
        temp_vars = temp_formula.variables()
        for temp_var in temp_vars:
            line = self.add_ug(Formula('A', temp_var, temp_formula), last_line)
            sub = temp_conversion[temp_var]
            temp_formula = temp_formula.substitute({temp_var:sub})
            last_line = self.add_universal_instantiation(temp_formula, line, sub)

        return last_line



    def add_substituted_equality(self, substituted: Union[Formula, str],
                                 line_number: int,
                                 parametrized_term: Union[Term, str]) -> \
            int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, whose two sides are the results of substituting the
        two respective sides of an equality from the specified already existing
        line of the proof into the given parametrized term.

        Parameters:
            substituted: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation.
            line_number: line number in the proof of an equality.
            parametrized_term: term parametrized by the constant name ``'_'``,
                specified as either a term or its string representation, such
                that substituting each of the two sides of the equality with the
                given line number into this parametrized term respectively
                yields each of the two sides of the given equality.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.

        Examples:
            If Line `line_number` contains the formula ``'g(x)=h(y)'`` and
            `parametrized_term` is ``'_+7'``, then `substituted` should be
            ``'g(x)+7=h(y)+7'``.
        """
        if isinstance(substituted, str):
            substituted = Formula.parse(substituted)
        assert is_equality(substituted.root)
        assert line_number < len(self._lines)
        equality = self._lines[line_number].formula
        assert is_equality(equality.root)
        if isinstance(parametrized_term, str):
            parametrized_term = Term.parse(parametrized_term)
        assert substituted == \
               Formula('=', [parametrized_term.substitute(
                                 {'_': equality.arguments[0]}),
                             parametrized_term.substitute(
                                 {'_': equality.arguments[1]})])
        # Task 10.8
                                                            #  parametrized_term:  plus('_', 0)
        line_formula = self._lines[line_number].formula     # c=d
        first = line_formula.arguments[0]
        second = line_formula.arguments[1]
        f_first = parametrized_term.substitute({'_': first})                             # plus(c, 0)
        rx_formula = Formula('=', [f_first, f_first])
        l1 = self.add_instantiated_assumption(rx_formula, Prover.RX, {'c': f_first})    # plus(c, 0)=plus(c, 0)
        f = Formula('->', line_formula, Formula('->', rx_formula, substituted))         # (c=d->(plus(c, 0)=plus(c, 0)->plus(c, 0)=plus(d, 0)))
        R = Formula('=', [f_first, parametrized_term])                                  # plus(c, 0)=plus('_', 0)
        l2 = self.add_instantiated_assumption(f, Prover.ME, {'R': R, 'c': first, 'd': second})
        l3 = self.add_mp(f.second, line_number, l2)
        l4 = self.add_mp(substituted, l1, l3)
        return l4





    def _add_chaining_of_two_equalities(self, line_number1: int,
                                        line_number2: int) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies an
        equality that is the result of chaining together two equalities from
        the specified already existing lines of the proof.

        Parameters:
            line_number1: line number in the proof of an equality of the form
                ``'``\ `first`\ ``=``\ `second`\ ``'``.
            line_number2: line number in the proof of an equality of the form
                ``'``\ `second`\ ``=``\ `third`\ ``'``.

        Returns:
            The line number of the newly appended line that justifies the
            equality ``'``\ `first`\ ``=``\ `third`\ ``'`` in the proof being
            created by the current prover.

        Examples:
            If Line `line_number1` contains the formula ``'a=b'`` and Line
            `line_number2` contains the formula ``'b=f(b)'``, then the last
            appended line will contain the formula ``'a=f(b)'``.
        """
        assert line_number1 < len(self._lines)
        equality1 = self._lines[line_number1].formula
        assert is_equality(equality1.root)
        assert line_number2 < len(self._lines)
        equality2 = self._lines[line_number2].formula
        assert is_equality(equality2.root)
        assert equality1.arguments[1] == equality2.arguments[0]
        # Task 10.9.1
        assump = self._lines[line_number1].formula
        assump2 = self._lines[line_number2].formula
        a = assump.arguments[0]
        b = assump.arguments[1]
        c = assump2.arguments[1]
        b_eq_a = Formula('=', [b, a])
        R = Formula('=', [Term('_'), c])
        l1 = self.add_flipped_equality(b_eq_a, line_number1)
        a_eq_c = Formula('=', [a, c])
        f = Formula('->', b_eq_a, Formula('->', assump2,a_eq_c ))
        l2 = self.add_instantiated_assumption(f, Prover.ME, {'R': R, 'c': b, 'd': a})
        l3 = self.add_mp(f.second, l1, l2)
        l4 = self.add_mp(a_eq_c, line_number2, l3)
        return l4




    def add_chained_equality(self, chained: Union[Formula, str],
                             line_numbers: Sequence[int]) -> int:
        """Appends to the proof being created by the current prover a sequence
        of validly justified lines, the last of which validly justifies the
        given equality, which is the result of chaining together equalities
        from the specified already existing lines of the proof.

        Parameters:
            chained: conclusion of the sequence of lines to be appended,
                specified as either a formula or its string representation,
                of the form ``'``\ `first`\ ``=``\ `last`\ ``'``.
            line_numbers: line numbers in the proof of equalities of the form
                ``'``\ `first`\ ``=``\ `second`\ ``'``,
                ``'``\ `second`\ ``=``\ `third`\ ``'``, ...,
                ``'``\ `before_last`\ ``=``\ `last`\ ``'``, i.e., the left-hand
                side of the first equality is the left-hand side of the given
                equality, the right-hand of each equality (except for the last)
                is the left-hand side of the next equality, and the right-hand
                side of the last equality is the right-hand side of the given
                equality.

        Returns:
            The line number of the newly appended line that justifies the given
            equality in the proof being created by the current prover.

            Examples:
            If `line_numbers` is ``[7,3,9]``, Line 7 contains the formula
            ``'a=b'``, Line 3 contains the formula ``'b=f(b)'``, and Line 9
            contains the formula ``'f(b)=0'``, then `chained` should be
            ``'a=0'``.
        """
        if isinstance(chained, str):
            chained = Formula.parse(chained)
        assert is_equality(chained.root)
        assert len(line_numbers) >= 2
        current_term = chained.arguments[0]
        for line_number in line_numbers:
            assert line_number < len(self._lines)
            equality = self._lines[line_number].formula
            assert is_equality(equality.root)
            assert equality.arguments[0] == current_term
            current_term = equality.arguments[1]
        assert chained.arguments[1] == current_term
        # Task 10.9.2
        last_line = line_numbers[0]
        for i in range(1, len(line_numbers)):
            last_line = self._add_chaining_of_two_equalities(last_line, line_numbers[i])

        return last_line

