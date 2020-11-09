# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Sequence, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

def formulas_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulas that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable `x` that is assigned the
    value ``False``.

    Parameters:
        model: model to construct the formulas for.

    Returns:
        A list of the constructed formulas, ordered alphabetically by variable
        name.

    Examples:
        >>> formulas_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    # Task 6.1a
    arr = [None]*len(model)
    for num, var in enumerate(sorted(model.keys())):
        if model[var]:
            arr[num] = Formula(var)
        else:
            arr[num] = Formula('~', Formula(var))
    return arr


def prove_in_model(formula: Formula, model:Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p->q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_in_model(Formula.parse('(p->q7)'),
        ...                        {'q7': False, 'p': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p->q7)
        >>> proof.statement.assumptions
        (~p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)
    # Task 6.1b
    vars = formulas_capturing_model(model)
    evaluation = evaluate(formula, model)
    if evaluation:
        conclusion = formula
    else:
        conclusion = Formula('~', formula)
    lines = []

    prove_in_model_helper(formula, model, lines)
    return Proof(InferenceRule(vars, conclusion), AXIOMATIC_SYSTEM, lines)


def prove_in_model_helper(formula, model, lines):
    """
    adds the proof lines to the lines list
    :param formula: the formula
    :param model: the model
    :param lines: array of the proof lines
    """
    p = formula.root
    eval = evaluate(formula, model)
    if is_variable(p):
        if model[p]:
            lines.append(Proof.Line(formula))
        else:
            lines.append(Proof.Line(Formula('~',formula)))
    elif is_unary(p):
        unary_case(eval, formula, lines, model)
    elif is_binary(p):
        binary_case(eval, formula, lines, model)


def binary_case(eval, formula, lines, model):
    """
    adds the necessary lines to the proofs in the binary case
    :param eval: the evaluation of the formula
    :param formula: the formula
    :param lines: array of the proof lines
    :param model: the model
    """
    phi = formula.first
    psi = formula.second
    if eval:
        positive_case(lines, model, phi, psi)
    else:
        negative_case(lines, model, phi, psi)



def negative_case(lines, model, phi, psi):
    """
    case that the evaluation of the formula is false
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    prove_in_model_helper(phi, model, lines)
    phi_line_num = len(lines) - 1
    prove_in_model_helper(psi, model, lines)
    minus_psi_line = len(lines) - 1
    form = Formula('->', phi, Formula('->', Formula('~', psi), Formula('~', Formula('->', phi, psi))))
    lines.append(Proof.Line(form, NI, []))
    ni_line = len(lines) - 1
    lines.append(Proof.Line(form.second, MP, [phi_line_num, ni_line]))
    lines.append(Proof.Line(form.second.second, MP, [minus_psi_line, len(lines) - 1]))


def positive_case(lines, model, phi, psi):
    """
    case that the evaluation of the formula is true
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    if not evaluate(phi, model):
        prove_in_model_helper(phi, model, lines)
        form = Formula('->', Formula('~', phi), Formula('->', phi, psi))
        lines.append(Proof.Line(form, I2, []))
    else:
        prove_in_model_helper(psi, model, lines)
        form = Formula('->', psi, Formula('->', phi,psi))
        lines.append(Proof.Line(form, I1, []))
    lines.append(Proof.Line(form.second, MP, [len(lines) - 2, len(lines) - 1]))


def unary_case(eval, formula, lines, model):
    """
    adds the necessary lines to the proofs in the unary case
    :param eval: the evaluation of the formula
    :param formula: the formula
    :param lines: array of the proof lines
    :param model: the model
    """
    if not eval:
        prove_in_model_helper(formula.first, model, lines)
        f = Formula('->', formula.first, Formula('~', Formula('~', formula.first)))
        lines.append(Proof.Line(f, NN, []))
        lines.append(Proof.Line(f.second, MP, [len(lines) - 2, len(lines) - 1]))

    else:
        prove_in_model_helper(formula.first, model, lines)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_from_negation: valid proof of `conclusion` from the same
            assumptions and inference rules of `proof_from_affirmation`, but
            with the last assumption being ``'~``\ `assumption` ``'`` instead of
            `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If `proof_from_affirmation` is of ``['p', '~q', 'r'] ==> '(p&(r|~r))'``,
        then `proof_from_negation` must be of
        ``['p', '~q', '~r'] ==> '(p&(r|~r))'`` and the returned proof is of
        ``['p', '~q'] ==> '(p&(r|~r))'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules
    # Task 6.2
    affirmation_proof = remove_assumption(proof_from_affirmation)
    lines = [line for line in affirmation_proof.lines]
    affirm_line_num  = len(lines)-1
    negation_proof =remove_assumption(proof_from_negation)
    for line in negation_proof.lines:
        new_line = Proof.Line(line.formula)
        if line.rule != None:
            new_line = Proof.Line(line.formula, line.rule, [i + affirm_line_num + 1 for i in line.assumptions])
        lines.append(new_line)
    neg_line_num = len(lines)-1
    map = {'q': affirmation_proof.statement.conclusion.first, 'p': affirmation_proof.statement.conclusion.second}
    formula = R.specialize(map).conclusion
    lines.append(Proof.Line(formula, R, []))
    r_line = len(lines)-1
    lines.append(Proof.Line(formula.second, MP, [affirm_line_num, r_line]))
    lines.append(Proof.Line(formula.second.second, MP, [neg_line_num, len(lines)-1]))

    return Proof(InferenceRule(proof_from_affirmation.statement.assumptions[:-1],
                               proof_from_affirmation.statement.conclusion),
                 proof_from_affirmation.rules.union({MP, I0, I1, D, R}), lines)

def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulas that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulas to prove.

    Returns:
        A valid proof of the given tautology from the formulas that capture the
        given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'),
        ...                         {'p': True, 'q': False})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        (p, ~q)
        >>> proof.rules == AXIOMATIC_SYSTEM
        True

        >>> proof = prove_tautology(Formula.parse('(~(p->p)->q)'))
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (~(p->p)->q)
        >>> proof.statement.assumptions
        ()
        >>> proof.rules == AXIOMATIC_SYSTEM
        True
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())
    # Task 6.3a
    vars = sorted(tautology.variables())
    if len(model) == len(vars):
        proof = prove_in_model(tautology, model)
    else:
        pos_model = {}
        neg_model = {}
        for key in sorted(model.keys()):
            pos_model[key] = model[key]
            neg_model[key] = model[key]

        for var in vars:
            if var not in model:
                pos_model[var] = True
                neg_model[var] = False
                break

        p1 = prove_tautology(tautology, pos_model)
        p2 = prove_tautology(tautology, neg_model)
        proof = reduce_assumption(p1, p2)
    return proof



def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})
    # Task 6.3b
    vars = list(formula.variables())
    models = all_models(vars)
    for model in models:
        if not evaluate(formula, model):
            return model
    p =  prove_tautology(formula, {})
    return p

def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))

        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    # Task 6.4a
    return encode_as_formula_helper(rule, 0)


def encode_as_formula_helper(rule, i):
    """
    :param rule: inference rule to encode.
    :param i: index of current assumption in rule
    :return: formula of kind "(assumption[i] -> assumption[i+1]...-> conclusion)"
    """
    if i == len(rule.assumptions):
        return rule.conclusion
    return Formula("->", rule.assumptions[i], encode_as_formula_helper(rule, i+1))



def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})
    # Task 6.4b
    tautology_formula = encode_as_formula(rule)
    p = prove_tautology(tautology_formula)
    lines = [line for line in p.lines]
    mp_lines(tautology_formula, rule, lines)
    return Proof(rule, AXIOMATIC_SYSTEM, lines)


def mp_lines(formula, rule, lines):
    """
    adds all the lines of the MP to the proof
    :param formula: current formula of kind: (x1->x2->x3->....->conclusion) where x_i is an assumption
    :param rule: sound inference rule whose assumptions and conclusion contain no
            constants or operators beyond ``'->'`` and ``'~'``, to prove.
    :param lines: the list of all the proofs lines
    """
    if formula != rule.conclusion:
        lines.append(Proof.Line(formula.first))
        lines.append(Proof.Line(formula.second, MP, [len(lines) - 1, len(lines) - 2]))
        mp_lines(formula.second, rule, lines)


def model_or_inconsistency(formulas: Sequence[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulas hold, or proves
    ``'~(p->p)'`` from these formulas.

    Parameters:
        formulas: formulas that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulas hold if such exists,
        otherwise a valid proof of ``'~(p->p)'`` from the given formulas via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})
    # Task 6.5
    vars = set()
    for formula in formulas:
        v = formula.variables()
        vars = vars.union(v)

    models = all_models(list(vars))
    for model in models:
        for num, formula in enumerate(formulas):
            if not evaluate(formula, model):
                break
            else:
                if num == len(formulas)-1:
                    return model

    rule = InferenceRule(formulas, Formula.parse("~(p->p)"))
    p = prove_sound_inference(rule)
    return p

def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulas
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'`` (and may contain constants), whose affirmation
            or negation is to prove.
        model: model from whose formulas to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a valid proof of the formula; otherwise a valid proof of
        ``'~``\ `formula`\ ``'``. The returned proof is from the formulas that
        capture the given model, in the order returned by
        `formulas_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.

    Examples:
        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': False, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        ~(p&q7)
        >>> proof.statement.assumptions
        (p, ~q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True

        >>> proof = prove_in_model_full(Formula.parse('(p&q7)'),
        ...                             {'q7': True, 'p': True})
        >>> proof.is_valid()
        True
        >>> proof.statement.conclusion
        (p&q7)
        >>> proof.statement.assumptions
        (p, q7)
        >>> proof.rules == AXIOMATIC_SYSTEM_FULL
        True
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
    vars = formulas_capturing_model(model)
    evaluation = evaluate(formula, model)
    if evaluation:
        conclusion = formula
    else:
        conclusion = Formula('~', formula)
    lines = []

    prove_in_model_full_helper(formula, model, lines)
    return Proof(InferenceRule(vars, conclusion), AXIOMATIC_SYSTEM_FULL, lines)


def prove_in_model_full_helper(formula, model, lines):
    """
    adds the proof lines to the lines list
    :param formula: the formula
    :param model: the model
    :param lines: array of the proof lines
    """
    p = formula.root
    eval = evaluate(formula, model)
    if is_variable(p):
        if model[p]:
            lines.append(Proof.Line(formula))
        else:
            lines.append(Proof.Line(Formula('~',formula)))
    elif is_constant(p):
        if p == 'T':
            lines.append(Proof.Line(formula, T, []))
        else:
            lines.append(Proof.Line(Formula('~', formula), NF, []))
    elif is_unary(p):
        unary_case_full(eval, formula, lines, model)
    elif is_binary(p):
        binary_case_full(eval, formula, lines, model)


def binary_case_full(eval, formula, lines, model):
    """
    adds the necessary lines to the proofs in the binary case
    :param eval: the evaluation of the formula
    :param formula: the formula
    :param lines: array of the proof lines
    :param model: the model
    """
    phi = formula.first
    psi = formula.second
    binary_op = formula.root
    if binary_op == '->':
        if eval:
            positive_case_implies(lines, model, phi, psi)
        else:
            negative_case_implies(lines, model, phi, psi)
    elif binary_op == '&':
        if eval:
            positive_case_and(lines, model, phi, psi)
        else:
            negative_case_and(lines, model, phi, psi)
    elif binary_op == '|':
        if eval:
            positive_case_or(lines, model, phi, psi)
        else:
            negative_case_or(lines, model, phi, psi)

def positive_case_or(lines, model, phi, psi):
    """
    case that the evaluation of the formula is true
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    if evaluate(phi, model):
        prove_in_model_full_helper(phi, model, lines)
        formula = Formula('->', phi, Formula('|', phi, psi))
        lines.append(Proof.Line(formula, O2, []))
    elif evaluate(psi, model):
        prove_in_model_full_helper(psi, model, lines)
        formula = Formula('->', psi, Formula('|', phi, psi))
        lines.append(Proof.Line(formula, O1, []))
    lines.append(Proof.Line(formula.second, MP, [len(lines)-2, len(lines)-1]))

def negative_case_or(lines, model, phi, psi):
    """
    case that the evaluation of the formula is true
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    prove_in_model_full_helper(Formula('~', phi), model, lines)
    phi_line_num = len(lines) - 1
    prove_in_model_full_helper(Formula('~', psi), model, lines)
    psi_line_num = len(lines) - 1
    formula = Formula('->', Formula('~', phi), Formula('->', Formula('~', psi), Formula('~', Formula('|', phi, psi))))
    lines.append(Proof.Line(formula, NO, []))
    lines.append(Proof.Line(formula.second, MP, [phi_line_num, len(lines)-1]))
    lines.append(Proof.Line(formula.second.second, MP, [psi_line_num, len(lines)-1]))

def negative_case_and(lines, model, phi, psi):
    """
    case that the evaluation of the formula is false
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    if not evaluate(phi, model):
        prove_in_model_full_helper(phi, model, lines)
        formula = Formula('->', Formula('~', phi), Formula('~', Formula('&', phi, psi)))
        lines.append(Proof.Line(formula, NA2, []))
    elif not evaluate(psi, model):
        prove_in_model_full_helper(psi, model, lines)
        formula = Formula('->', Formula('~', psi), Formula('~', Formula('&', phi, psi)))
        lines.append(Proof.Line(formula, NA1, []))
    lines.append(Proof.Line(formula.second, MP, [len(lines)-2, len(lines)-1]))

def positive_case_and(lines, model, phi, psi):
    """
    case that the evaluation of the formula is true
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    prove_in_model_full_helper(phi, model, lines)
    phi_line_num = len(lines) - 1
    prove_in_model_full_helper(psi, model, lines)
    psi_line_num = len(lines) - 1
    formula = Formula('->', phi, Formula('->', psi, Formula('&', phi, psi)))
    lines.append(Proof.Line(formula, A, []))
    lines.append(Proof.Line(formula.second, MP, [phi_line_num, len(lines)-1]))
    lines.append(Proof.Line(formula.second.second, MP, [psi_line_num, len(lines)-1]))

def unary_case_full(eval, formula, lines, model):
    """
    adds the necessary lines to the proofs in the unary case
    :param eval: the evaluation of the formula
    :param formula: the formula
    :param lines: array of the proof lines
    :param model: the model
    """
    if not eval:
        prove_in_model_full_helper(formula.first, model, lines)
        f = Formula('->', formula.first, Formula('~', Formula('~', formula.first)))
        lines.append(Proof.Line(f, NN, []))
        lines.append(Proof.Line(f.second, MP, [len(lines) - 2, len(lines) - 1]))

    else:
        prove_in_model_full_helper(formula.first, model, lines)


def negative_case_implies(lines, model, phi, psi):
    """
    case that the evaluation of the formula is false
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    prove_in_model_full_helper(phi, model, lines)
    phi_line_num = len(lines) - 1
    prove_in_model_full_helper(psi, model, lines)
    minus_psi_line = len(lines) - 1
    form = Formula('->', phi, Formula('->', Formula('~', psi), Formula('~', Formula('->', phi, psi))))
    lines.append(Proof.Line(form, NI, []))
    ni_line = len(lines) - 1
    lines.append(Proof.Line(form.second, MP, [phi_line_num, ni_line]))
    lines.append(Proof.Line(form.second.second, MP, [minus_psi_line, len(lines) - 1]))


def positive_case_implies(lines, model, phi, psi):
    """
    case that the evaluation of the formula is true
    :param lines: array of the proof lines
    :param model: the model
    :param phi: formula.first
    :param psi: formula.second
    """
    if not evaluate(phi, model):
        prove_in_model_full_helper(phi, model, lines)
        form = Formula('->', Formula('~', phi), Formula('->', phi, psi))
        lines.append(Proof.Line(form, I2, []))
    else:
        prove_in_model_full_helper(psi, model, lines)
        form = Formula('->', psi, Formula('->', phi, psi))
        lines.append(Proof.Line(form, I1, []))
    lines.append(Proof.Line(form.second, MP, [len(lines) - 2, len(lines) - 1]))


