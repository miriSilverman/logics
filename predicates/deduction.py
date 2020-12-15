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
    print(proof.assumptions)
    print("proof.conclusion: ", proof.conclusion)
    print("assumption: ", assumption)

    phi = assumption

    new_assumptions = set()
    for assum in proof.assumptions:
        if assum != assumption:
            new_assumptions.add(assum)

    prover = Prover(new_assumptions, print_as_proof_forms)

    line_conversion_map = {}    # {old_line_num: new_line_num}

    for num, line in enumerate(proof.lines):
        f = line.formula
        if f == phi:
            l = prover.add_tautology(Formula('->', f, f))
            line_conversion_map[num] = l
        elif type(line) == Proof.MPLine:

            first_assump_num = line_conversion_map[line.antecedent_line_number]
            second_assump_num = line_conversion_map[line.conditional_line_number]

            phi_imp_alpha = prover._lines[first_assump_num] .formula    # phi -> alpha
            phi_imp_alpha_imp_beta = prover._lines[first_assump_num].formula        # phi->(alpha->beta)
            phi_imp_beta = Formula('->', phi, phi_imp_alpha_imp_beta.second.second)     # phi->beta

            form = Formula('->', phi_imp_alpha_imp_beta, Formula('->', phi_imp_alpha, phi_imp_beta))
            l1 = prover.add_tautology(form)   # phi->(alpha->beta)---> ((phi -> alpha) -> (phi->beta))
            l2 = prover.add_mp(form.second, second_assump_num, l1)  # ((phi -> alpha) -> (phi->beta))
            l3 = prover.add_mp(form.second.second, first_assump_num, l2)    #  (phi->beta)
            line_conversion_map[num] = l3

        elif type(line) == Proof.AssumptionLine:
            alpha = line.formula
            step1 = prover.add_assumption(alpha)  # alpha
            step2 = prover.add_tautology(Formula('->', alpha, Formula('->', phi, alpha)))
            step3 = prover.add_mp(Formula('->', phi, alpha), step1, step2)  # phi->alpha
            line_conversion_map[num] = step3

        elif type(line) == Proof.UGLine:
            formula = line.formula  # Ax[alpha]
            alpha = formula.predicate   # alpha
            alpha_new_line_num = line_conversion_map[line.predicate_line_number]    # phi->alpha  line num in new proof
            x = formula.variable
            ug_formula = Formula('A', x, alpha)
            line1 = prover.add_ug(ug_formula, alpha_new_line_num)   # Ax[phi->alpha]
            line2 = prover.add_instantiated_assumption(Formula('->', ug_formula, Formula('->', phi, formula)),
                        Prover.US, {'Q': phi, 'R': alpha, 'x': x})   # Ax[phi->alpha] -> (phi->Ax[alpha])
            line3 = prover.add_mp(Formula('->', phi, formula), line1, line2)    # phi->Ax[alpha]
            line_conversion_map[num] = line3

    print("miri")

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
