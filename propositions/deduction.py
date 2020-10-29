# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a

    rules = antecedent_proof.rules.union({conditional})
    lines = list(antecedent_proof.lines)
    formula = Formula.parse("("+str(antecedent_proof.statement.conclusion)+"->"+str(consequent)+")")
    lines.append(Proof.Line(formula, conditional, []))
    lines.append(Proof.Line(Formula.parse(str(consequent)), MP, [len(lines)-2, len(lines)-1]))

    return Proof(InferenceRule(antecedent_proof.statement.assumptions, consequent), rules, lines)





def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    rules = antecedent1_proof.rules.union(antecedent2_proof.rules).union({double_conditional})

    formula1 = Formula.parse("(" + str(antecedent2_proof.statement.conclusion) + "->" + str(consequent) + ")")
    formula = Formula.parse("(" + str(antecedent1_proof.statement.conclusion) + "->" + str(formula1) + ")")

    lines = list(antecedent1_proof.lines)       # lines of proof1
    lines.append(Proof.Line(formula, double_conditional, []))       # imply
    lines.append(Proof.Line(formula1, MP, [len(lines) - 2, len(lines) - 1]))    #conclusion 1
    con_1_line_num = len(lines)  # line number of conclusion 1


    for line in antecedent2_proof.lines:    # adding lines of proof 2
        new_line = Proof.Line(line.formula)
        if line.rule != None:
            new_line = Proof.Line(line.formula, line.rule, [i + con_1_line_num for i in line.assumptions])
        lines.append(new_line)
    con_2_line_num = len(lines) - 1       # line number of conclusion 2

    lines.append(Proof.Line(Formula.parse(str(consequent)), MP, [con_2_line_num, con_1_line_num - 1]))

    return Proof(InferenceRule(antecedent1_proof.statement.assumptions, consequent), rules, lines)



def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    rules_without_assumptions = rules_with_no_assumptions(proof)

    psi = proof.statement.assumptions[-1]
    lines_map = {}      # {old_line_num: new_line_num}
    lines = []
    for num, line in enumerate(proof.lines):
        formula = line.formula
        if formula == psi:
            lines.append(Proof.Line(Formula.parse("("+str(formula)+"->"+str(formula)+")"), I0, []))
        elif line.formula in proof.statement.assumptions or line.rule in rules_without_assumptions:
            add_lines_case_2(line, lines, psi)
        elif line.rule == MP:
            add_lines_case_3(line, lines, lines_map, num, proof, psi)
        lines_map[num] = len(lines) - 1

    statement = InferenceRule(proof.statement.assumptions[:-1],
                              Formula.parse("("+str(proof.statement.assumptions[-1])+"->"+
                                            str(proof.statement.conclusion)+")"))
    return Proof(statement, proof.rules.union({I0,I1, D, MP}), lines)




def add_lines_case_3(line, lines, lines_map, num, proof, psi):
    """
    adds the necessary lines to the current proof in order to convert the line 'line'
    in the old proof to a line '(psi->line)'
    :param line: current line in the old proof
    :param lines: the list of all lines of the new proof
    :param lines_map: {num_of_line_in_the_old_proof: num_of_ the converted_line(psi->line)_in_the_new_proof}
    :param num: num of this current line in the old proof
    :param proof:the old proof
    :param psi: the last assumption of the old proof
    """
    map = {'p': psi, 'q': proof.lines[line.assumptions[0]].formula,
           'r': line.formula}
    d = D.specialize(map).conclusion
    lines.append(Proof.Line(d, D, []))
    lines.append(Proof.Line(d.second, MP, [lines_map[proof.lines[num].assumptions[1]], len(lines) - 1]))
    first = lines_map[proof.lines[num].assumptions[0]]
    second = len(lines) - 1
    lines.append(Proof.Line(d.second.second, MP, [first, second]))


def add_lines_case_2(line, lines, psi):
    """
    adds the necessary lines to the current proof in order to convert the line 'line'
    in the old proof to a line '(psi->line)'
    :param line: current line in the old proof
    :param lines: the list of all lines of the new proof
    :param psi: the last assumption of the old proof
    """
    lines.append(line)
    lines.append(Proof.Line(Formula.parse("(" + str(line.formula) + "->(" + str(psi) + "->" + str(line.formula) + "))"),
                            I1, []))
    lines.append(Proof.Line(Formula.parse("(" + str(psi) + "->" + str(line.formula) + ")"), MP,
                            [len(lines) - 2, len(lines) - 1]))


def rules_with_no_assumptions(proof):
    """
    :param proof: a proof
    :return: the rules from the proofs rules that have no assumptions
    """
    rules_without_assumptions = []
    for rule in proof.rules:
        if not rule.assumptions:
            rules_without_assumptions.append(rule)
    return rules_without_assumptions


def prove_from_opposites(proof_of_affirmation: Proof,
                         proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    lines = [line for line in proof_of_negation.lines]      # lines of proof_of_negation
    negate_line_mum = len(lines) - 1
    statement = InferenceRule(proof_of_affirmation.statement.assumptions, conclusion)
    rules = proof_of_negation.rules.union(proof_of_affirmation.rules).union({MP, I2})

    for line in proof_of_affirmation.lines:     # lines of proof_of_affirmation
        new_line = Proof.Line(line.formula)
        if line.rule != None:
            new_line = Proof.Line(line.formula, line.rule, [i+1+ negate_line_mum for i in line.assumptions])
        lines.append(new_line)
    affirm_line_num = len(lines) - 1

    i_2_formula = Formula.parse("("+str(proof_of_negation.statement.conclusion) +
                                          "->("+str(proof_of_affirmation.statement.conclusion)+
                                          "->"+str(conclusion)+"))")

    lines.append(Proof.Line(i_2_formula, I2, []))
    lines.append(Proof.Line(i_2_formula.second, MP, [negate_line_mum, len(lines) - 1]))
    lines.append(Proof.Line(conclusion, MP, [affirm_line_num, len(lines) - 1]))

    return Proof(statement, rules, lines)


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    proof_as_deduction = remove_assumption(proof)

    p_implies_p_formula = proof_as_deduction.statement.conclusion.second.first
    psi_formula = proof_as_deduction.statement.conclusion.first.first

    lines = [line for line in proof_as_deduction.lines]     # lines of deduction
    line_of_deduction_conclusion = len(lines)-1

    formula = Formula.parse("("+str(proof_as_deduction.statement.conclusion) +"->("+
                            str(p_implies_p_formula) +"->"+ str(psi_formula)+"))")

    lines.append(Proof.Line(formula, N, []))
    line_of_n = len(lines)-1
    lines.append(Proof.Line(p_implies_p_formula, I0, []))
    line_of_p_implies_p = len(lines)-1
    lines.append(Proof.Line(formula.second, MP, [line_of_deduction_conclusion, line_of_n]))
    lines.append(Proof.Line(psi_formula, MP, [line_of_p_implies_p, len(lines)-1]))


    return Proof(InferenceRule(proof.statement.assumptions[:-1], psi_formula), proof.rules.union({I0, I1,D,N}), lines)



