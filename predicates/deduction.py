# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """        
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1
    phi = assumption
    prover = Prover(proof.assumptions, print_as_proof_forms)
    line_conversion_map = {}    # {old_line_num: new_line_num}

    for num, line in enumerate(proof.lines):
        f = line.formula

        if f == phi or type(line) == Proof.TautologyLine:
            l = prover.add_tautology(Formula('->', phi, f))
            line_conversion_map[num] = l

        elif type(line) == Proof.MPLine:
            manage_mp_line(line, line_conversion_map, num, phi, proof, prover)

        elif type(line) == Proof.AssumptionLine:
            manage_assumption_line(line, line_conversion_map, num, phi, prover)

        elif type(line) == Proof.UGLine:
            manage_ug_line(line, line_conversion_map, num, phi, prover)

    new_assumptions = set()
    for assum in proof.assumptions:
        if assum.formula != phi:
            new_assumptions.add(assum)

    return Proof(new_assumptions, Formula('->', phi, proof.conclusion), prover._lines)


def manage_ug_line(line, line_conversion_map, num, phi, prover):
    """
    adds the relevant lines in case of a ug line
    Args:
        line: the current line in the original proof
        line_conversion_map: {old line num: new line num}
        num: number of the current line in the original proof
        phi: the assumption to remove
        prover: the proof of phi->origin_conclusion without the assumption phi
    """
    formula = line.formula  # Ax[alpha]
    alpha = formula.predicate  # alpha
    alpha_new_line_num = line_conversion_map[line.predicate_line_number]  # phi->alpha  line num in new proof
    phi_imp_alpha = prover._lines[alpha_new_line_num].formula
    x = formula.variable
    ug_formula = Formula('A', x, phi_imp_alpha)
    line1 = prover.add_ug(ug_formula, alpha_new_line_num)  # Ax[phi->alpha]
    foo = Formula('->', ug_formula, Formula('->', phi, Formula('A', x, alpha)))
    line2 = prover.add_instantiated_assumption(foo, Prover.US, {'Q': phi, 'R': alpha.substitute({x: Term('_')}),
                                                                'x': x})  # Ax[phi->alpha] -> (phi->Ax[alpha])
    line3 = prover.add_mp(Formula('->', phi, formula), line1, line2)  # phi->Ax[alpha]
    line_conversion_map[num] = line3


def manage_assumption_line(line, line_conversion_map, num, phi, prover):
    """
    adds the relevant lines in case of an assumption line
    Args:
        line: the current line in the original proof
        line_conversion_map: {old line num: new line num}
        num: number of the current line in the original proof
        phi: the assumption to remove
        prover: the proof of phi->origin_conclusion without the assumption phi
    """
    alpha = line.formula
    if line.assumption != None:
        step1 = prover.add_instantiated_assumption(alpha, line.assumption, line.instantiation_map)
    else:
        step1 = prover.add_assumption(alpha)  # alpha
    step2 = prover.add_tautology(Formula('->', alpha, Formula('->', phi, alpha)))  # alpha->(phi->alpha)
    step3 = prover.add_mp(Formula('->', phi, alpha), step1, step2)  # phi->alpha
    line_conversion_map[num] = step3


def manage_mp_line(line, line_conversion_map, num, phi, proof, prover):
    """
    adds the relevant lines in case of a mp line
    Args:
        line: the current line in the original proof
        line_conversion_map: {old line num: new line num}
        num: number of the current line in the original proof
        phi: the assumption to remove
        prover: the proof of phi->origin_conclusion without the assumption phi
    """
    alpha = proof.lines[line.antecedent_line_number].formula
    alpha_imp_beta = proof.lines[line.conditional_line_number].formula
    beta = alpha_imp_beta.second
    first_assump_num = line_conversion_map[line.antecedent_line_number]  # phi -> alpha
    second_assump_num = line_conversion_map[line.conditional_line_number]  # phi->(alpha->beta)
    phi_imp_alpha = prover._lines[first_assump_num].formula  # phi -> alpha
    phi_imp_alpha_imp_beta = Formula('->', phi, Formula('->', alpha, beta))  # phi->(alpha->beta)
    phi_imp_beta = Formula('->', phi, beta)  # phi->beta
    form = Formula('->', phi_imp_alpha_imp_beta, Formula('->', phi_imp_alpha, phi_imp_beta))
    l1 = prover.add_tautology(form)  # phi->(alpha->beta)---> ((phi -> alpha) -> (phi->beta))
    l2 = prover.add_mp(form.second, second_assump_num, l1)  # ((phi -> alpha) -> (phi->beta))
    l3 = prover.add_mp(form.second.second, first_assump_num, l2)  # (phi->beta)
    line_conversion_map[num] = l3


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2

    not_phi = assumption
    phi = Formula('~', assumption)
    not_axiom = proof.conclusion
    axiom = Formula('~', not_axiom)

    prover = Prover(proof.assumptions, False)

    proof_of_not_phi_imp_not_axsiom = remove_assumption(proof, not_phi)

    for line in proof_of_not_phi_imp_not_axsiom.lines:
        l = prover._add_line(line)

    not_phi_imp_not_axiom_line_num = len(prover._lines)-1   # conclusion: (~phi)->(~axiom)
    not_phi_imp_not_axiom_formula = prover._lines[not_phi_imp_not_axiom_line_num].formula
    axiom_imp_phi = Formula('->', axiom, phi)

    # l1 = (~phi)->(~axiom)
    l2 = prover.add_tautology(Formula('->',not_phi_imp_not_axiom_formula, axiom_imp_phi))  # (~phi->~axiom)->(axiom->phi)
    l3 = prover.add_mp(axiom_imp_phi, not_phi_imp_not_axiom_line_num, l2)  # axiom->phi
    l4 = prover.add_tautology(axiom)        # axiom
    l5 = prover.add_mp(phi, l4, l3)         # phi


    new_assumptions = set()
    for assum in proof.assumptions:
        if assum.formula != assumption:
            new_assumptions.add(assum)

    return Proof(new_assumptions, Formula('~', assumption), prover._lines)