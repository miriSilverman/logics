# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: propositions/some_proofs.py

"""Some proofs in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.deduction import *

# Some inference rules that only use conjunction.

#: Conjunction introduction inference rule
A_RULE = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                       Formula.parse('(x&y)'))
#: Conjunction elimination (right) inference rule
AE1_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
#: Conjunction elimination (left) inference rule
AE2_RULE = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))

def prove_and_commutativity() -> Proof:
    """Proves ``'(q&p)'`` from ``'(p&q)'`` via `A_RULE`, `AE2_RULE`, and
    `AE1_RULE`.

    Returns:
        A valid proof of ``'(q&p)'`` from the single assumption ``'(p&q)'`` via
        the inference rules `A_RULE`, `AE2_RULE`, and `AE1_RULE`.
    """
    # Task 4.7
    lines = [None]*4
    p = Formula('p')
    q = Formula('q')
    lines[0] = Proof.Line(Formula('&', p, q))
    lines[1] = Proof.Line(q, AE1_RULE, [0])
    lines[2] = Proof.Line(p, AE2_RULE, [0])
    lines[3] = Proof.Line(Formula('&', q, p), A_RULE , [1, 2])
    return Proof(InferenceRule([lines[0].formula], lines[3].formula), {A_RULE, AE1_RULE, AE2_RULE}, lines)

def offending_line(proof):
    """Finds the first invalid line in the given proof.

    Parameters:
        proof: proof to search.

    Returns:
        An error message containing the line number and string representation of
        the first invalid line in the given proof, or ``None`` if all the lines
        of the given proof are valid."""
    for i in range(len(proof.lines)):
        if not proof.is_line_valid(i):
            return "Invalid Line " + str(i) + ": " + str(proof.lines[i])
    return None

def prove_I0() -> Proof:
    """Proves `~propositions.axiomatic_systems.I0` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I0` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 4.8
    lines = [None] * 5
    goal = Formula('->', Formula('p'), Formula('p'))
    psi =Formula('->', Formula('p'), Formula('->', goal, Formula('p')))
    phi = Formula('->', Formula('p'), goal)

    lines[0] = Proof.Line(psi, I1, [])
    lines[1] = Proof.Line(Formula('->', psi, Formula('->', phi, goal)), D, [])
    lines[2] = Proof.Line(Formula('->', phi, goal), MP, [0,1])
    lines[3] = Proof.Line(phi, I1, [])
    lines[4] = Proof.Line(goal, MP, [3, 2])

    return Proof(InferenceRule([], goal), {MP, I1, D}, lines)


#: Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism() -> Proof:
    """Proves `HS` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    and `~propositions.axiomatic_systems.D`.

    Returns:
        A valid proof of `HS` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    # Task 5.5
    lines = [None]*5
    p = Formula('p')
    q = Formula('q')
    r = Formula('r')
    lines[0] = Proof.Line(p)
    lines[1] = Proof.Line(Formula('->', p, q))
    lines[2] = Proof.Line(q, MP, [0,1])
    lines[3] = Proof.Line(Formula('->', q, r))
    lines[4] = Proof.Line(r, MP, [2,3])

    p = Proof(InferenceRule([lines[1].formula, lines[3].formula, p], r),
             {MP, I0, I1, D}, lines)
    return remove_assumption(p)


def prove_I2() -> Proof:
    """Proves `~propositions.axiomatic_systems.I2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.I2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7a
    lines = [None] * 5
    lines[0] = Proof.Line(Formula.parse("~p"))
    lines[1] = Proof.Line(Formula.parse("(~p->(~q->~p))"), I1, [])
    lines[2] = Proof.Line(Formula.parse("(~q->~p)"), MP, [0,1])
    lines[3] = Proof.Line(Formula.parse("((~q->~p)->(p->q))"), N, [])
    lines[4] = Proof.Line(Formula.parse("(p->q)"), MP, [2,3])
    p =Proof(InferenceRule([Formula.parse('(~p->(~q->~p))'), Formula.parse('((~q->~p)->(p->q))'), Formula.parse('~p')],
                           Formula.parse('(p->q)')), {MP, I0, I1, N, D}, lines)
    p = remove_assumption(p)
    return Proof(InferenceRule([], p.statement.conclusion), {MP, I0, I1, N, D}, p.lines)


#: Double-negation elimination
_NNE = InferenceRule([], Formula.parse('(~~p->p)'))

def _prove_NNE() -> Proof:
    """Proves `_NNE` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_NNE` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7b
    lines = [None] * 8
    lines[0] = Proof.Line(Formula.parse("~~p"))
    lines[1] = Proof.Line(Formula.parse("(~~p->(~~~~p->~~p))"), I1, [])
    lines[2] = Proof.Line(Formula.parse("(~~~~p->~~p)"), MP, [0, 1])
    lines[3] = Proof.Line(Formula.parse("((~~~~p->~~p)->(~p->~~~p))"), N, [])
    lines[4] = Proof.Line(Formula.parse("(~p->~~~p)"), MP, [2, 3])
    lines[5] = Proof.Line(Formula.parse("((~p->~~~p)->(~~p->p))"), N, [])
    lines[6] = Proof.Line(Formula.parse("(~~p->p)"), MP, [4, 5])
    lines[7] = Proof.Line(Formula.parse("p"), MP, [0, 6])

    p = Proof(InferenceRule([Formula.parse('~~p')], Formula.parse('p')),
              {MP, I0, I1, D, N}, lines)
    return remove_assumption(p)


def prove_NN() -> Proof:
    """Proves `~propositions.axiomatic_systems.NN` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NN` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7c
    lines = []
    lines.append(Proof.Line(Formula.parse("~~~p")))
    lines.append(Proof.Line(Formula.parse("(~~~p->(~~~~~p->~~~p))"), I1, []))
    lines.append(Proof.Line(Formula.parse("(~~~~~p->~~~p)"), MP, [0, 1]))
    lines.append(Proof.Line(Formula.parse("((~~~~~p->~~~p)->(~~p->~~~~p))"), N, []))
    lines.append(Proof.Line(Formula.parse("(~~p->~~~~p)"), MP, [2, 3]))
    lines.append(Proof.Line(Formula.parse("((~~p->~~~~p)->(~~~p->~p))"), N, []))
    lines.append(Proof.Line(Formula.parse("(~~~p->~p)"), MP, [4, 5]))
    lines.append(Proof.Line(Formula.parse("~p"), MP, [0, 6]))

    p = Proof(InferenceRule([Formula.parse('~~~p')], Formula.parse('~p')),
              {MP, I0, I1, D, N}, lines)
    p = remove_assumption(p)
    lines = [line for line in p.lines]

    lines.append(Proof.Line(Formula.parse("((~~~p->~p)->(p->~~p))"), N, []))
    lines.append(Proof.Line(Formula.parse("(p->~~p)"), MP, [len(lines)-2, len(lines)-1]))
    return Proof(InferenceRule([], Formula.parse('(p->~~p)')), {MP, I0, I1, D, N}, lines)




#: Contraposition
_CP = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def _prove_CP() -> Proof:
    """Proves `_CP` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CP` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7d
    p = _prove_NNE()
    lines = [line for line in p.lines]
    con1_line = len(lines)-1        # (~~p->p)
    form1_line = lines[-1]

    p = prove_specialization(prove_NN(), InferenceRule([], Formula.parse("(q->~~q)")))
    add_lines_of_proof(con1_line, lines, p)
    con2_line = len(lines)-1        # (q->~~q)
    form2_line = lines[-1]

    p = prove_specialization(prove_hypothetical_syllogism(), InferenceRule([Formula.parse("(~~p->p)"),
                                                                            Formula.parse("(p->q)")],
                                                                           Formula.parse("(~~p->q)")))

    for line in p.lines:
        new_line = add_lines2(con2_line, form1_line, line)
        lines.append(new_line)

    con4_line = len(lines)-1        # (~~p->q)
    form4_line = lines[-1]

    p = prove_specialization(prove_hypothetical_syllogism(), InferenceRule([Formula.parse("(~~p->q)"),
                                                                            Formula.parse("(q->~~q)")],
                                                                           Formula.parse("(~~p->~~q)")))

    for line in p.lines:
        new_line = add_lines3(con4_line, form2_line, form4_line, line)
        lines.append(new_line)

    p = Proof(InferenceRule([Formula.parse('(p->q)')], Formula.parse('(~~p->~~q)')),
              {MP, I0, I1, D, N}, lines)
    p = remove_assumption(p)

    lines = [line for line in p.lines]
    form6_line = lines[-1]

    lines.append(Proof.Line(Formula.parse("((~~p->~~q)->(~q->~p))"), N, []))
    con7_line = len(lines)-1  # ((~~p->~~q)->(~q->~p))
    form7_line = lines[-1]
    p = prove_specialization(prove_hypothetical_syllogism(), InferenceRule([Formula.parse("((p->q)->(~~p->~~q))"),
                                           Formula.parse("((~~p->~~q)->(~q->~p))")],
                                          Formula.parse("((p->q)->(~q->~p))")))
    add_lines4(con7_line, form2_line, form4_line, form6_line, form7_line, lines, p)

    return Proof(InferenceRule([], Formula.parse("((p->q)->(~q->~p))")), {MP, I0, I1, D, N}, lines)


def add_lines1(con2_line, line):
    new_line = Proof.Line(line.formula)
    if line.rule != None:
        new_line = Proof.Line(line.formula, line.rule, [i + con2_line + 1 for i in line.assumptions])
    return new_line


def add_lines2(con2_line, form1_line, line):
    new_line = add_lines1(con2_line, line)
    if line.formula == Formula.parse("(~~p->p)"):
        new_line = form1_line
    return new_line


def add_lines3(con4_line, form2_line, form4_line, line):
    new_line = add_lines1(con4_line, line)
    if line.formula == Formula.parse("(~~p->q)"):
        new_line = form4_line
    if line.formula == Formula.parse("(q->~~q)"):
        new_line = form2_line
    return new_line


def add_lines4(con7_line, form2_line, form4_line, form6_line, form7_line, lines, p):
    for line in p.lines:
        new_line = add_lines3(con7_line, form2_line, form4_line, line)
        if line.formula == Formula.parse("((p->q)->(~~p->~~q))"):
            new_line = form6_line
        if line.formula == Formula.parse("((~~p->~~q)->(~q->~p))"):
            new_line = form7_line
        lines.append(new_line)


def print_lines(lines):
    for i, line in enumerate(lines):
        if i in {22, 46}:
            print()
        print(i, ") ", line)


def add_lines_of_proof(con1_line, lines, p):
    for line in p.lines:
        new_line = add_lines1(con1_line, line)
        lines.append(new_line)



def prove_NI() -> Proof:
    """Proves `~propositions.axiomatic_systems.NI` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NI` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7e




#: Consequentia mirabilis
_CM = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def _prove_CM() -> Proof:
    """Proves `_CM` via `~propositions.axiomatic_systems.MP`,
    `~propositions.axiomatic_systems.I0`, `~propositions.axiomatic_systems.I1`,
    `~propositions.axiomatic_systems.D`, and
    `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `_CM` via the inference rules
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7f

def prove_R() -> Proof:
    """Proves `~propositions.axiomatic_systems.R` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.R` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    # Optional Task 6.7g

def prove_N() -> Proof:
    """Proves `~propositions.axiomatic_systems.N` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    and `~propositions.axiomatic_systems.N_ALTERNATIVE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.N` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N_ALTERNATIVE`.
    """
    # Optional Task 6.8

def prove_NA1() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA1` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE1`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA1` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE1`.
    """
    # Optional Task 6.9a

def prove_NA2() -> Proof:
    """Proves `~propositions.axiomatic_systems.NA2` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.AE2`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NA2` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.AE2`.
    """
    # Optional Task 6.9b

def prove_NO() -> Proof:
    """Proves `~propositions.axiomatic_systems.NO` via
    `~propositions.axiomatic_systems.MP`, `~propositions.axiomatic_systems.I0`,
    `~propositions.axiomatic_systems.I1`, `~propositions.axiomatic_systems.D`,
    `~propositions.axiomatic_systems.N`, and
    `~propositions.axiomatic_systems.OE`.

    Returns:
        A valid proof of `~propositions.axiomatic_systems.NO` via the inference
        rules `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.OE`.
    """
    # Optional Task 6.9c
