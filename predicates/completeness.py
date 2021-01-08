# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *
import itertools


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants

def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    return is_primitively_closed(sentences) and \
           is_universally_closed(sentences) and \
           is_existentially_closed(sentences)

def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.1

    constants = list(get_constants(sentences))
    relations = set()
    for sentence in sentences:
        s = sentence.relations()
        for relation in s:
            relations.add(relation)

    for relation in relations:
        relation_name = relation[0]
        args_num = relation[1]

        for i in itertools.product(constants, repeat=args_num):
            args = list(i)
            f = Formula(relation_name, args)
            neg_f = Formula('~', f)
            if f not in sentences and neg_f not in sentences:
                return False

    return True

def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence of the given
        sentences, and for every constant name from the given sentences, the
        predicate of this quantified sentence, with every free occurrence of the
        universal quantification variable replaced with this constant name, is
        one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.2
    constants = list(get_constants(sentences))

    for formula in sentences:
        if is_quantifier(formula.root) and formula.root == 'A':
            pred = formula.predicate
            x = formula.variable
            for constant in constants:
                new_formula = pred.substitute({x : Term(constant)})
                if new_formula not in sentences:
                    return False
    return True



def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence of the given
        sentences there exists a constant name such that the predicate of this
        quantified sentence, with every free occurrence of the existential
        quantification variable replaced with this constant name, is one of the
        given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.1.3
    constants = list(get_constants(sentences))
    for formula in sentences:
        had_a_constant = False
        if is_quantifier(formula.root) and formula.root == 'E':
            pred = formula.predicate
            x = formula.variable
            for constant in constants:
                new_formula = pred.substitute({x : Term(constant)})
                if new_formula in sentences:
                    had_a_constant = True
            if not had_a_constant:
                return False
    return True


def find_unsatisfied_quantifier_free_sentence(sentences: Container[Formula],
                                              model: Model[str],
                                              unsatisfied: Formula) -> Formula:
    """
    Given a closed set of prenex-normal-form sentences, given a model whose
    universe is the set of all constant names from the given sentences, and
    given a sentence from the given set that the given model does not satisfy,
    finds a quantifier-free sentence from the given set that the given model
    does not satisfy.
    
    Parameters:
        sentences: closed set of prenex-normal-form sentences, which is only to
            be accessed using containment queries, i.e., using the ``in``
            operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given sentences that is not
        satisfied by the given model.
    """
    # We assume that every sentence in sentences is of type formula, is in
    # prenex normal form, and has no free variables, and furthermore that the
    # set of constants that appear somewhere in sentences is model.universe;
    # but we cannot assert these since we cannot iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    constants = model.universe
    root = unsatisfied.root

    if not is_quantifier(root):
        return unsatisfied

    if is_quantifier(root):
        if root == 'A':
            for constant in constants:
                pred = unsatisfied.predicate
                x = unsatisfied.variable
                assigned = pred.substitute({x: Term(constant)})
                assigned_is_true_in_model = model.evaluate_formula(assigned)
                if not assigned_is_true_in_model:
                    f = find_unsatisfied_quantifier_free_sentence(sentences, model, assigned)
                    return f

        elif root == 'E':
            for constant in constants:
                pred = unsatisfied.predicate
                x = unsatisfied.variable
                assigned = pred.substitute({x: Term(constant)})
                assigned_is_true_in_model = model.evaluate_formula(assigned)
                if not assigned_is_true_in_model:
                    if assigned in sentences:
                        f = find_unsatisfied_quantifier_free_sentence(sentences, model, assigned)
                        return f


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula whose subformulas are to
            be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of the given
        quantifier-free formula.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    # Task 12.3.1
    root = quantifier_free.root
    if is_binary(root):
        first_primitives = get_primitives(quantifier_free.first)
        second_primitives = get_primitives(quantifier_free.second)
        return first_primitives.union(second_primitives)
    if is_unary(root):
        first_primitives = get_primitives(quantifier_free.first)
        return first_primitives
    else:
        return {quantifier_free}


def model_or_inconsistency(sentences: AbstractSet[Formula]) -> \
        Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences to either find a
            model for or prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """    
    assert is_closed(sentences)
    # Task 12.3.2
    constants = get_constants(sentences)

    universe = {c for c in constants}
    constants_meanings  = dict()
    for c in constants:
        constants_meanings[c] = c
    primitive_sentences = set()
    relations_meanings = dict()
    for formula in sentences:
        relations = formula.relations()
        for r in relations:
            relations_meanings[r[0]] = set()
        if is_relation(formula.root) or (is_unary(formula.root) and is_relation(formula.first.root)):
            primitive_sentences.add(formula)

    for p in sentences:
        if is_relation(p.root):
            args = tuple(str(c) for c in p.arguments)
            relations_meanings[p.root].add(args)


    model = Model(universe, constants_meanings, relations_meanings)

    if model.is_model_of(sentences):
        return model

    prover = Prover(Prover.AXIOMS.union(sentences), False)

    for s in sentences:
        if not model.evaluate_formula(s):
            lines_nums = set()
            f = find_unsatisfied_quantifier_free_sentence(sentences, model, s)  # f not satisfied and quantified free
            l1 = prover.add_assumption(f)   # s not satisfied in the model
            lines_nums.add(l1)
            primitives_in_f = get_primitives(f)
            primitives_in_sentences_that_in_f = set()
            for primitive in primitive_sentences:
                if primitive in primitives_in_f :
                    primitives_in_sentences_that_in_f.add(primitive)
                    li = prover.add_assumption(primitive)
                    lines_nums.add(li)
                if is_unary(primitive.root):
                    first = primitive.first
                    if first in primitives_in_f:
                        primitives_in_sentences_that_in_f.add(primitive)
                        li = prover.add_assumption(primitive)
                        lines_nums.add(li)

                if is_relation(primitive.root):
                    if Formula('~', primitive) in primitives_in_f:
                        primitives_in_sentences_that_in_f.add(primitive)
                        li = prover.add_assumption(primitive)
                        lines_nums.add(li)

            concatenation = concatenate_and(list({f}.union(primitives_in_sentences_that_in_f)), 0)

            concat_line = prover.add_tautological_implication(concatenation, lines_nums)
            tautology = Formula('~', concatenation)

            tautology_line = prover.add_tautology(tautology)
            contradiction = prover.add_tautological_implication(Formula('&', concatenation, tautology), {concat_line, tautology_line})
            return prover.qed()
    # concatenation = concatenate_and(list(sentences), 0)
    # tautology = Formula('~', concatenation)
    #
    # prover = Prover(Prover.AXIOMS)
    # print(tautology)
    # prover.add_tautology(tautology)
    # return prover.qed()

def concatenate_and(sentences, idx: int):
    if idx == len(sentences) - 1:
        return sentences[idx]
    return Formula('&', sentences[idx], concatenate_and(sentences, idx+1))

if __name__ == '__main__':
    f1 = Formula.parse("~Plus(0)")
    f2 = Formula.parse("Plus(0)")
    mode = Model({'0'}, {'0': '0'}, {'Plus': set()})
    # i = mode.is_model_of({f1})
    # print(i)
    # f3 = Formula.parse("Plus(2)")
    # f4 = Formula.parse("Plus(3)")
    s = {f1, f2}
    p = model_or_inconsistency(s)
    print(p)
    # f = concatenate_and([f1, f2, f3, f4], 0)
    # print(f)

def combine_contradictions(proof_from_affirmation: Proof,
                           proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption `assumption` replaced with its negation
            ``'~``\ `assumption` ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions)
    assert len(common_assumptions) == \
           len(proof_from_affirmation.assumptions) - 1
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions.difference(common_assumptions))[0]
    negated_assumption = list(
        proof_from_negation.assumptions.difference(common_assumptions))[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == \
           Formula('~', affirmed_assumption.formula)
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union({affirmed_assumption,
                                                negated_assumption}):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4

def eliminate_universal_instantiation_assumption(proof: Proof, constant: str,
                                                 instantiation: Formula,
                                                 universal: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is a universal
    instantiation of the former, to a proof of a contradiction from the same
    assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        instantiation: assumption of the given proof that is obtained from the
            predicate of `universal` by replacing all free occurrences of the
            universal quantification variable by some constant.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `instantiation`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(instantiation) in proof.assumptions
    assert Schema(universal) in proof.assumptions
    assert universal.root == 'A'
    assert instantiation == \
           universal.predicate.substitute({universal.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained replacing in the predicate of any universally quantified
        sentence from the given sentences, all occurrences of the quantification
        variable with some constant from the given sentences.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.6

def replace_constant(proof: Proof, constant: str, variable: str = 'zz') -> \
        Proof:
    """Replaces all occurrences of the given constant in the given proof with
    the given variable.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in given the proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7.1

def eliminate_existential_witness_assumption(proof: Proof, constant: str,
                                             witness: Formula,
                                             existential: Formula) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is an existential
    witness of the former, to a proof of a contradiction from the same
    assumptions without `witness`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        witness: assumption of the given proof that is obtained from the
            predicate of `existential` by replacing all free occurrences of the
            existential quantification variable by some constant that does not
            appear in any assumption of the given proof except for this
            assumption.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        proof except `witness`.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert Schema(witness) in proof.assumptions
    assert Schema(existential) in proof.assumptions
    assert existential.root == 'E'
    assert witness == \
           existential.predicate.substitute(
               {existential.variable: Term(constant)})
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    for assumption in proof.assumptions.difference({Schema(witness)}):
        assert constant not in assumption.formula.constants()
    # Task 12.7.2

def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentences from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the predicate of that quantified sentence by replacing all
        occurrences of the quantification variable with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert is_in_prenex_normal_form(sentence) and \
               len(sentence.free_variables()) == 0
    # Task 12.8
