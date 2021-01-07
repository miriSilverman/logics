# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))

def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3.1
    root = formula.root
    if is_unary(root):
        return is_quantifier_free(formula.first)
    elif is_binary(root):
        first = is_quantifier_free(formula.first)
        second = is_quantifier_free(formula.second)
        return first and second
    elif is_quantifier(root):
        return False
    else:
        return True


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3.2
    if is_quantifier_free(formula):
        return True
    elif is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)
    else:
        return False

def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))

def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())
    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)

def _uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.5
    return _uniquely_rename_quantified_variables_helper(formula, set())


def _uniquely_rename_quantified_variables_helper(formula: Formula, vars_to_change: set) -> \
        Tuple[Formula, Proof]:
    root = formula.root
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)

    if is_variable(root) or is_constant(root) or is_relation(root) or is_equality(root):
        f = Formula('->', formula, formula)
        l1 = prover.add_tautology(f)
        l2 = prover.add_tautological_implication(Formula('&', f, f), {l1})
        return formula, Proof(assumptions, equivalence_of(formula, formula), prover._lines)

    elif is_quantifier(root):   # Ax[phi]
        x = formula.variable
        phi = formula.predicate
        psi, psi_proof = _uniquely_rename_quantified_variables_helper(phi, vars_to_change)
        l1 = prover.add_proof(psi_proof.conclusion, psi_proof)   # phi <-> psi

        phi_eq_psi = equivalence_of(phi, psi)   # phi <-> psi

        if root == 'A':
            eq, line_eq = quantifier_all_case(formula, l1, phi, phi_eq_psi, prover, psi, x) # Ax[phi(x)] <-> Ax[psi(x)]
        elif root == 'E':
            eq, line_eq = quantifier_exist_case(l1, phi, phi_eq_psi, prover, psi, x)    # Ex[phi(x)] <-> Ex[psi(x)]

        cur_formula = Formula(root, x, psi)   # root x[psi(x)]
        if x in vars_to_change:
            cur_formula, eq = renaming(cur_formula, formula, line_eq, prover, psi, root, x) # converts x to z

        return cur_formula, Proof(assumptions, eq, prover._lines)


    elif is_unary(root):
        first, first_proof = _uniquely_rename_quantified_variables_helper(formula.first, vars_to_change)
        l1 = prover.add_proof(first_proof.conclusion, first_proof)  # origin_first <-> first
        new_formula = Formula(root, first)
        eq = equivalence_of(formula, new_formula)
        prover.add_tautological_implication(eq, {l1})
        return new_formula, Proof(assumptions, eq, prover._lines)

    elif is_binary(root):
        first, l1, l2, second = recuesively_uniqely_first_and_second(formula, prover, vars_to_change)
        cur_formula = Formula(root, first, second)  # (first * second)
        eq = equivalence_of(formula, cur_formula)
        prover.add_tautological_implication(eq, {l1, l2})
        return cur_formula, Proof(assumptions, eq, prover._lines)


def recuesively_uniqely_first_and_second(formula, prover, vars_to_change):
    origin_second_free_vars = formula.second.variables().union(vars_to_change)
    if is_quantifier(formula.second.root):
        origin_second_free_vars = origin_second_free_vars.union({formula.second.variable})
    first, first_proof = _uniquely_rename_quantified_variables_helper(formula.first, origin_second_free_vars)
    l1 = prover.add_proof(first_proof.conclusion, first_proof)  # origin_first <-> first
    first_free_vars = first.variables().union(vars_to_change)
    if is_quantifier(first.root):
        first_free_vars = first_free_vars.union({first.variable})
    second, second_proof = _uniquely_rename_quantified_variables_helper(formula.second, first_free_vars)
    l2 = prover.add_proof(second_proof.conclusion, second_proof)  # origin_second <-> second
    return first, l1, l2, second


def renaming(cur_formula, formula, line_eq, prover, psi, root, x):
    """
        proves Ax[phi(x)] <-> Az[psi(z)]"
    """
    z = next(fresh_variable_name_generator)
    Rz = psi.substitute({x: Term(z)})  # psi(z)
    new_formula = Formula(root, z, Rz)  # Az[psi(z)]
    R = Rz.substitute({z: Term('_')})  # psi(_)
    if root == 'A':
        equivalent_proof_line = prove_eq_all_rename_var(R, cur_formula, Rz, prover, new_formula,
                                                    x, z)  # "Ax[psi(x)] <-> Az[psi(z)]"
    elif root == 'E':
        equivalent_proof_line = prove_equ_exist_case(R, cur_formula, Rz, prover, new_formula, x,
                                                     z)  # "Ex[psi(x)] <-> Ez[psi(z)]"

    cur_formula = new_formula
    eq = equivalence_of(formula, cur_formula)
    prover.add_tautological_implication(eq, {line_eq, equivalent_proof_line})  # "Ax[phi(x)] <-> Az[psi(z)]"
    return cur_formula, eq



def prove_equ_exist_case(R, Rz, first, prover, quantified_new_first, x, z):
    """
    proves Ex[R(x)]] <-> Ez[R(z)]
    Returns:

    """
    #############       Ez[R(z)] -> Ex[R(x)]]       ###########
    pred = Formula('->', first, Rz)  # R(z)->Ex[R(x)]
    s1 = prover.add_instantiated_assumption(pred, Prover.EI, {'R': R, 'x': x, 'c': z})  # R(z)->Ex[R(x)]
    form = Formula('A', z, pred)  # Az[R(z)->Ex[R(x)]]
    s2 = prover.add_ug(form, s1)  # Az[R(z)->Ex[R(x)]]
    and_form = Formula('&', form, quantified_new_first)  # Az[R(z)->Ex[R(x)]] & Ez[R(z)]
    imp_form = Formula('->', and_form, Rz)  # Az[R(z)->Ex[R(x)]] & Ez[R(z)] -> Ex[R(x)]
    s3 = prover.add_instantiated_assumption(imp_form, Prover.ES, {'Q': Rz, 'R': R, 'x': z})  # Az[R(z)->Ex[R(x)]] & Ez[R(z)] -> Ex[R(x)]

    s4 = prover.add_tautological_implication(Formula('->', quantified_new_first, Rz),
                                             {s2, s3})  # Ez[R(z)] -> Ex[R(x)]]

    ##########     Ex[R(x)]] -> Ez[R(z)]    ###########
    pred2 = Formula('->', Rz.predicate, quantified_new_first)  # R(x)->Ez[R(z)]
    s5 = prover.add_instantiated_assumption(pred2, Prover.EI, {'R': R, 'x': z, 'c': x})  # R(x)->Ez[R(z)]
    form2 = Formula('A', x, pred2)  # Ax[R(x)->Ez[R(z)]]
    s6 = prover.add_ug(form2, s5)  # Ax[R(x)->Ez[R(z)]]
    and_form2 = Formula('&', form2, Rz)  # Ax[R(x)->Ez[R(z)]] & Ex[R(x)]
    imp_form2 = Formula('->', and_form2, quantified_new_first)  # Ax[R(x)->Ez[R(z)]] & Ex[R(x)] -> Ez[R(z)]
    s7 = prover.add_instantiated_assumption(imp_form2, Prover.ES,
                            {'Q': quantified_new_first, 'R': R, 'x': x})  # Ax[R(x)->Ez[R(z)]] & Ex[R(x)] -> Ez[R(z)]


    s8 = prover.add_tautological_implication(Formula('->', Rz, quantified_new_first), {s6, s7})  # Ex[R(x)]] -> Ez[R(z)]


    l11 = prover.add_tautological_implication(equivalence_of(Rz, quantified_new_first), {s4, s8}) # Ex[R(x)]] <-> Ez[R(z)]
    return l11


def quantifier_exist_case(l1, phi, phi_eq_psi, prover, psi, x):
    """
    proves: Ex[phi] <-> Ex[psi]
    Args:
        l1:  line in the proof that proves: phi <-> psi
        phi: phi
        phi_eq_psi:  phi <-> psi
        prover: the prover
        psi: psi
        x: the variable of the exist

    Returns: the formula Ex[phi] <-> Ex[psi]

    """
    assump16 = Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                                    '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
                      {'x', 'y', 'R', 'Q'})
    Exphi_eq_Expsi = equivalence_of(Formula('E', x, phi), Formula('E', x, psi))  # Ex[phi] <-> Ex[psi]
    form = Formula('->', phi_eq_psi, Exphi_eq_Expsi)
    l2 = prover.add_instantiated_assumption(form, assump16, {'x': x, 'y': x, 'R': phi.substitute({x: Term('_')}),
                                                             'Q': psi.substitute({x: Term(
                                                                 '_')})})  # (phi <-> psi) -> (Ex[phi] <-> Ex[psi])
    l3 = prover.add_mp(Exphi_eq_Expsi, l1, l2)  # Ex[phi] <-> Ex[psi]
    return Exphi_eq_Expsi, l3


def quantifier_all_case(formula, l1, phi, phi_eq_psi, prover, psi, x):
    """
    proves: Ax[phi] <-> Ax[psi]
    Args:
        l1:  line in the proof that proves: phi <-> psi
        phi: phi
        phi_eq_psi:  phi <-> psi
        prover: the prover
        psi: psi
        x: the variable of the exist

    Returns: the formula Ax[phi] <-> Ax[psi]

    """
    assump15 = Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                                    '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'), {'x', 'y', 'R', 'Q'})
    Axphi_eq_Axpsi = equivalence_of(Formula('A', x, phi), Formula('A', x, psi))  # Ax[phi] <-> Ax[psi]
    form = Formula('->', phi_eq_psi, Axphi_eq_Axpsi)
    l2 = prover.add_instantiated_assumption(form, assump15, {'x': x, 'y': x, 'R': phi.substitute({x: Term('_')}),
                                                             'Q': psi.substitute({x: Term(
                                                                 '_')})})  # (phi <-> psi) -> (Ax[phi] <-> Ax[psi])
    l3 = prover.add_mp(Axphi_eq_Axpsi, l1, l2)  # Ax[phi] <-> Ax[psi]
    return Axphi_eq_Axpsi, l3




def prove_eq_all_rename_var(R, first, new_first, prover, quantified_new_first, x, z):
    """
    proves: Ax[R(x)]<->Az[R(z)]

    """

    ######################      Ax[R(x)]->Az[R(z)]   #########################
    us = Formula('->', first, new_first)  # Ax[R(x)]->R(z)
    l3 = prover.add_instantiated_assumption(us, Prover.UI, {'R': R, 'x': x, 'c': z})  # Ax[R(x)]->R(z)
    general_us = Formula('A', z, us)
    l4 = prover.add_ug(general_us, l3)  # Az[Ax[R(x)]->R(z)]
    conc_us = Formula('->', general_us,
                      Formula('->', first, quantified_new_first))  # Az[Ax[R(x)]->R(z)] -> Ax[R(x)]->Az[R(z)]
    l5 = prover.add_instantiated_assumption(conc_us, Prover.US, {'Q': first, 'R': R, 'x': z})
    l6 = prover.add_mp(conc_us.second, l4, l5)  # Ax[R(x)]->Az[R(z)]

    ######################     Ax[R(x)]->Az[R(z)]    #########################
    us2 = Formula('->', quantified_new_first, first.predicate)  # Az[R(z)]->R(x)
    l7 = prover.add_instantiated_assumption(us2, Prover.UI, {'R': R, 'x': z, 'c': x})  # Az[R(z)]->R(x)
    general_us2 = Formula('A', x, us2)
    l8 = prover.add_ug(general_us2, l7)  # Ax[Az[R(z)]->R(x)]
    conc_us2 = Formula('->', general_us2, Formula('->', quantified_new_first,
                                                  first))  # Ax[Az[R(z)]->R(x)] -> Az[R(z)]->Ax[R(x)]
    l9 = prover.add_instantiated_assumption(conc_us2, Prover.US, {'Q': quantified_new_first, 'R': R, 'x': x})
    l10 = prover.add_mp(conc_us2.second, l8, l9)  # Ax[R(x)]->Az[R(z)]

    ######## conclusion   ########
    l11 = prover.add_tautological_implication(equivalence_of(first, quantified_new_first),
                                              {l6, l10})  # Ax[R(x)]<->Az[R(z)]
    return l11



def _pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    first = formula.first
    root = first.root
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)

    if is_quantifier_free(first):
        eq = equivalence_of(formula, formula)
        prover.add_tautology(eq)
        return formula, Proof(assumptions, eq, prover._lines)

    elif is_quantifier(root):   # ~Ax[R(x)] ------> Ex[~R(x)]
        x = first.variable
        phi = first.predicate
        phi_neg = Formula('~', phi)     # ~R(x)
        R = phi.substitute({x:Term('_')})

        new_phi, proof =_pull_out_quantifications_across_negation(phi_neg)   # equivalent to ~R(x) in the right format
        equivalence_neg_phi_and_new_phi = proof.conclusion
        pred_eq_line = prover.add_proof(equivalence_neg_phi_and_new_phi, proof)    # ~R(x) <-> new_phi


        if root == 'A':
            axiom = Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'), {'x', 'R'})
            eq_formula = Formula('E', x, Formula('~', phi))  # Ex[~R(x)]
            f = equivalence_of(formula, eq_formula) # ~Ax[R(x)] <-> Ex[~R(x)]
            equ_form, l2 = quantifier_exist_case(pred_eq_line, phi_neg, equivalence_neg_phi_and_new_phi,
                                                 prover, new_phi, eq_formula.variable)


        elif root == 'E':
            axiom = Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'), {'x', 'R'})
            eq_formula =  Formula('A', x, Formula('~', phi)) # Ex[~R(x)]
            f = equivalence_of(formula, eq_formula) # ~Ex[R(x)] <-> Ax[~R(x)]
            equ_form, l2 = quantifier_all_case(formula, pred_eq_line, phi_neg, equivalence_neg_phi_and_new_phi,
                                               prover, new_phi, eq_formula.variable)

        l1 = prover.add_instantiated_assumption(f, axiom, {'x': x, 'R': R})  # ~Ax[R(x)] <-> Ex[~R(x)]

        quantified_new_phi = Formula(eq_formula.root, eq_formula.variable, new_phi)   # Ex[new_phi]

        conclusion_formula_equivalence = equivalence_of(formula, quantified_new_phi)
        l3 = prover.add_tautological_implication(conclusion_formula_equivalence, {l1, l2}) # ~Ax[R(x)] <-> Ex[new_phi]


        return quantified_new_phi, Proof(assumptions, conclusion_formula_equivalence, prover._lines)



def _pull_out_quantifications_from_left_across_binary_operator(formula:
                                                               Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    first = formula.first
    root = formula.root
    first_root = first.root
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)

    if is_quantifier_free(first):
        eq = equivalence_of(formula, formula)
        prover.add_tautology(eq)
        return formula, Proof(assumptions, eq, prover._lines)

    elif is_quantifier(first_root):
        phi = first.predicate
        psi = formula.second
        x = first.variable


        all_and = Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                             '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'})
        exist_and = Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                             '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'})
        all_or = Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                             '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'})
        exist_or = Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                             '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'})
        all_implies = Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                             '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'})
        exist_implies = Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                             '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'})


        quant, scheme = preprocessing(all_and, all_implies, all_or, exist_and, exist_implies, exist_or, first_root,
                                      root)

        phi_root_psi = Formula(root, phi, psi)   #  Ax[phi] & psi ---> Ax [phi&psi]
        f, proof = _pull_out_quantifications_from_left_across_binary_operator(phi_root_psi)  # phi & psi

        eq_f_phi_and_psi = proof.conclusion # (phi & psi) <-> f
        l1 = prover.add_proof(eq_f_phi_and_psi, proof) # (phi & psi) <-> f

        eq_formula_phi_and_psi = equivalence_of(formula, Formula(quant, x, phi_root_psi))  # (Ax[phi] & psi) <-> Ax[phi & psi]

        l2 = prover.add_instantiated_assumption(eq_formula_phi_and_psi, scheme, {'x': x,
                            'R': phi.substitute({x: Term('_')}), 'Q': psi}) # (Ax[phi] & psi) <-> Ax[phi & psi]

        quantified_f = Formula(quant, x, f)    # Ax[f]

        l3 = calc_right_equivalence(eq_f_phi_and_psi, f, first_root, formula, l1, phi_root_psi, prover, root, x)

        eq_formula_f = equivalence_of(formula, quantified_f)   # (Ax[phi] & psi) <->  Ax[f]
        l4 = prover.add_tautological_implication(eq_formula_f, {l2, l3})  # (Ax[phi] & psi) <->  Ax[f]

        return quantified_f, Proof(assumptions, eq_formula_f, prover._lines)


def calc_right_equivalence(eq_f_phi_and_psi, f, first_root, formula, l1, phi_root_psi, prover, root, x):
    """
        proves the right equivalence according to the roots

    """
    if root in {'&', '|'}:
        if first_root == 'A':
            Axphi_and_psi_eq_Axf, l3 = quantifier_all_case(formula, l1, phi_root_psi, eq_f_phi_and_psi, prover, f,
                                                           x)  # Ax[phi & psi] <-> Ax[f]
        elif first_root == 'E':
            Axphi_and_psi_eq_Axf, l3 = quantifier_exist_case(l1, phi_root_psi, eq_f_phi_and_psi, prover, f,
                                                             x)  # Ex[phi & psi] <-> Ex[f]
    if root == '->':
        if first_root == 'E':
            Axphi_and_psi_eq_Axf, l3 = quantifier_all_case(formula, l1, phi_root_psi, eq_f_phi_and_psi, prover,
                                                           f, x)  # Ax[phi -> psi] <-> Ax[f]
        elif first_root == 'A':
            Axphi_and_psi_eq_Axf, l3 = quantifier_exist_case(l1, phi_root_psi, eq_f_phi_and_psi, prover, f,
                                                             x)  # Ex[phi -> psi] <-> Ex[f]
    return l3


def preprocessing(all_and, all_implies, all_or, exist_and, exist_implies, exist_or, first_root, root):
    """

        returns the relevant quantifier and scheme for the proof

    """
    if root == '&':
        if first_root == 'A':
            scheme = all_and
            quant = 'A'

        elif first_root == 'E':
            scheme = exist_and
            quant = 'E'


    elif root == '|':
        if first_root == 'A':
            scheme = all_or
            quant = 'A'

        elif first_root == 'E':
            scheme = exist_or
            quant = 'E'


    elif root == '->':
        if first_root == 'A':
            quant = 'E'
            scheme = all_implies
        elif first_root == 'E':
            quant = 'A'
            scheme = exist_implies
    return quant, scheme


def _pull_out_quantifications_from_right_across_binary_operator(formula:
                                                                Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    second = formula.second
    root = formula.root
    second_root = second.root
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)

    if is_quantifier_free(second):
        eq = equivalence_of(formula, formula)
        prover.add_tautology(eq)
        return formula, Proof(assumptions, eq, prover._lines)

    elif is_quantifier(second_root):    # (psi & Ax[phi])
        phi = second.predicate
        psi = formula.first
        x = second.variable

        all_and = Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x','R','Q'})
        exist_and = Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x','R','Q'})
        all_or = Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x','R','Q'})
        exist_or = Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x','R','Q'})
        all_implies = Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x','R','Q'})
        exist_implies = Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x','R','Q'})

        quant, scheme = preprocessing(all_and, all_implies, all_or, exist_and, exist_implies, exist_or, second_root,
                                      root)
        quant = second_root

        psi_root_phi = Formula(root, psi, phi)

        f, proof = _pull_out_quantifications_from_right_across_binary_operator(psi_root_phi)  # psi & phi

        eq_f_psi_and_phi = proof.conclusion  # (psi & phi) <-> f
        l1 = prover.add_proof(eq_f_psi_and_phi, proof)  # (psi & phi) <-> f

        eq_formula_phi_and_psi = equivalence_of(formula,
                                                Formula(quant, x, psi_root_phi))  # (psi & Ax[phi]) <-> Ax[psi & phi]

        l2 = prover.add_instantiated_assumption(eq_formula_phi_and_psi, scheme, {'x': x,
                                                                                 'R': phi.substitute({x: Term('_')}),
                                                                                 'Q': psi}) # (psi & Ax[phi]) <-> Ax[psi & phi]

        quantified_f = Formula(quant, x, f)  # Ax[f]

        if second_root == 'A':
            Axphi_and_psi_eq_Axf, l3 = quantifier_all_case(formula, l1, psi_root_phi, eq_f_psi_and_phi, prover, f,
                                                           x)  # Ax[psi & phi] <-> Ax[f]
        elif second_root == 'E':
            Axphi_and_psi_eq_Axf, l3 = quantifier_exist_case(l1, psi_root_phi, eq_f_psi_and_phi, prover, f,
                                                             x)  # Ex[psi & phi] <-> Ex[f]


        eq_formula_f = equivalence_of(formula, quantified_f)  # (psi & Ax[phi]) <->  Ax[f]
        l4 = prover.add_tautological_implication(eq_formula_f, {l2, l3})  # (psi & Ax[phi]) <->  Ax[f]

        return quantified_f, Proof(assumptions, eq_formula_f, prover._lines)


def _pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)
    # formula:  (quant_first[phi] & quant_second[psi])

    formula_no_left_quantifiers, left_proof = _pull_out_quantifications_from_left_across_binary_operator(formula) # quant_first[ psi & quant_second[phi] ]
    l1 = prover.add_proof(left_proof.conclusion, left_proof) # (quant_first[phi] & quant_second[psi]) <-> quant_first[ psi & quant_second[phi] ]

    binary_formula = reducing_quantifiers(formula_no_left_quantifiers)  # psi & quant_second[phi]

    formula_no_right_quantifiers, left_proof = _pull_out_quantifications_from_right_across_binary_operator(binary_formula)  # quant_second[ phi & psi ]
    l2 = prover.add_proof(left_proof.conclusion, left_proof)    #   psi & quant_second[phi] <-> quant_second[phi & psi ]

    # quant_first[ psi & quant_second[phi] ] <-> quant_first[ quant_second[phi & psi ] ]
    eq_quant, l3 = prove_equality_extra_quantified(formula_no_left_quantifiers, formula_no_right_quantifiers, l2, prover)


    # (quant_first[phi] & quant_second[psi]) <->  quant_first[ quant_second[phi & psi ] ]
    eq = equivalence_of(formula, eq_quant.first.second)
    p1 = prover._lines[l1].formula
    p2 = prover._lines[l3].formula

    # print("p1", p1)
    # print("p2", p2)
    l4 = prover.add_tautological_implication(eq, {l1, l3})
    return eq_quant.first.second, Proof(assumptions, eq, prover._lines)



def reducing_quantifiers(formula: Formula) -> Formula:
    if is_quantifier(formula.root):
        return reducing_quantifiers(formula.predicate)
    else:
        return formula

def prove_equality_extra_quantified(formula, first_psi, line_of_phi_eq_psi, prover):
    """
        formula:  quant_first[ psi & quant_second[phi] ]
        first psi: quant_second[ phi & psi ]
        proves that if  phi<->psi   then  Ex[Ay[Az...[phi]]] <-> Ex[Ay[Az...[psi]]]
    """
    # quant_first[ psi & quant_second[phi] ] <-> quant_first[ quant_second[phi & psi ] ]

    # formula <-> quant_second[ first_psi]
    quantifiers = []    # ["Ax", "Ey", "Ez"]
    cur_formula = formula   # at the end-->  (psi & quant_second[phi])
    while is_quantifier(cur_formula.root):
        quantifiers.append(cur_formula.root+cur_formula.variable)
        cur_formula = cur_formula.predicate


    last_line = line_of_phi_eq_psi
    phi = cur_formula # (psi & quant_second[phi]) ---> quant_first[ psi & quant_second[phi]]
    psi = first_psi # quant_second[ phi & psi ] -----> quant_first[ quant_second[phi & psi ] ]
    for i in reversed(quantifiers):
        if i[0] == 'A':
            x = i[1:]
            Axphi_eq_Axpsi, last_line = quantifier_all_case(formula, last_line, phi, equivalence_of(phi, psi), prover, psi, x)
            phi = Formula('A', x, phi)
            psi = Formula('A', x, psi)
        elif i[0] == 'E':
            x = i[1:]
            Axphi_eq_Axpsi, last_line = quantifier_exist_case(last_line, phi, equivalence_of(phi, psi), prover, psi, x)
            phi = Formula('E', x, phi)
            psi = Formula('E', x, psi)
    return equivalence_of(phi, psi), last_line



def _to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9
    root = formula.root
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)

    if is_quantifier_free(formula):
        eq = equivalence_of(formula, formula)
        prover.add_tautology(eq)
        return formula, Proof(assumptions, eq, prover._lines)

    if is_unary(root): # ~phi
        psi, proof =_to_prenex_normal_form_from_uniquely_named_variables(formula.first) # psi: prenex format
        l1 = prover.add_proof(proof.conclusion, proof)  # phi <-> psi

        new_f = Formula('~', psi)
        l2 = prover.add_tautological_implication(equivalence_of(formula, new_f), {l1}) # ~phi <-> ~psi
        prenexed_formula, proof_eq = _pull_out_quantifications_across_negation(new_f)
        l3 = prover.add_proof(proof_eq.conclusion, proof_eq) # ~psi <-> prenexed_formula

        eq = equivalence_of(formula, prenexed_formula)
        l3 = prover.add_tautological_implication(eq, {l1, l2, l3})   # ~phi <-> prenexed_formula

        return prenexed_formula, Proof(assumptions, eq, prover._lines)

    elif is_binary(root):
        prenexed_first, first_proof =_to_prenex_normal_form_from_uniquely_named_variables(formula.first) # psi: prenex format
        l1 = prover.add_proof(first_proof.conclusion, first_proof) # first <-> prenexed_first
        prenexed_second, second_proof =_to_prenex_normal_form_from_uniquely_named_variables(formula.second) # psi: prenex format
        l2 = prover.add_proof(second_proof.conclusion, second_proof) # second <-> prenexed_second

        new_binary_formula = Formula(root, prenexed_first, prenexed_second)
        l3 = prover.add_tautological_implication(equivalence_of(formula, new_binary_formula), {l1, l2})    # formula <-> new_binary_formula

        prenexed_binary, binary_proof = _pull_out_quantifications_across_binary_operator(new_binary_formula)
        l4 = prover.add_proof(binary_proof.conclusion, binary_proof) # new_binary_formula <-> prenexed_binary
        eq = equivalence_of(formula, prenexed_binary)
        l5 = prover.add_tautological_implication(eq, {l3, l4})    # formula <-> prenexed_binary
        return prenexed_binary, Proof(assumptions, eq, prover._lines)



    elif is_quantifier(root):
        prenexed_predicate, proof_pred = _to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
        pred_eq = proof_pred.conclusion
        l1 = prover.add_proof(pred_eq, proof_pred) # predicate <-> prenexed_predicate

        x = formula.variable
        prenexed_formula = Formula(root, x, prenexed_predicate)


        if root == 'A': # formula <-> prenexed_formula
            quantified_eq, l3 = quantifier_all_case(formula, l1, formula.predicate, pred_eq, prover, prenexed_predicate, x)

        elif root == 'E':
            quantified_eq, l3 = quantifier_exist_case(l1, formula.predicate, pred_eq, prover, prenexed_predicate, x)

        return prenexed_formula, Proof(assumptions, equivalence_of(formula, prenexed_formula), prover._lines)




def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 11.10
    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)
    uniquely_formula, proof_uniquely = _uniquely_rename_quantified_variables(formula)
    l1 = prover.add_proof(proof_uniquely.conclusion, proof_uniquely) # formula <-> uniquely_formula
    prenexed_uniquely, proof = _to_prenex_normal_form_from_uniquely_named_variables(uniquely_formula)
    l2 = prover.add_proof(proof.conclusion, proof)  # uniquely_formula <-> prenexed_uniquely
    eq = equivalence_of(formula, prenexed_uniquely)
    l3 = prover.add_tautological_implication(eq, {l1, l2})
    return prenexed_uniquely, Proof(assumptions, eq, prover._lines)
