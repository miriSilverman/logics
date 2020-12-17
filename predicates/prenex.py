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
    print("formula: ", formula)
    root = formula.root

    assumptions = Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS)
    prover = Prover(assumptions, False)

    if is_variable(root) or is_constant(root) or is_relation(root) or is_equality(root):
        print("!!!! in var/const/relation/equality   !!!!!")
        f = Formula('->', formula, formula)
        l1 = prover.add_tautology(f)
        l2 = prover.add_tautological_implication(Formula('&', f, f), {l1})
        print("vars done with ", formula)
        return formula, Proof(assumptions, equivalence_of(formula, formula), prover._lines)

    elif is_quantifier(root):
        print("!!!! in quantifier   !!!!!")

        x = formula.variable
        phi = formula.predicate
        psi, p = _uniquely_rename_quantified_variables(phi)
        l1 = prover.add_proof(p.conclusion, p)   # phi <-> psi

        phi_eq_psi = prover._lines[l1].formula
        if root == 'A':
            Axphi_eq_Axpsi = quantifier_all_case(formula, l1, phi, phi_eq_psi, prover, psi, x)
            return Formula(root, formula.variable, psi), Proof(assumptions, Axphi_eq_Axpsi, prover._lines)

        elif root == 'E':
            Exphi_eq_Expsi = quantifier_exist_case(l1, phi, phi_eq_psi, prover, psi, x)
            return Formula(root, formula.variable, psi), Proof(assumptions, Exphi_eq_Expsi, prover._lines)


    elif is_binary(root):
        print("!!!! in binary   !!!!!")

        first, l1, l2, second = create_new_firs_and_second(formula, prover)
        the_new_formula = Formula(root, first, second)

        first_free_vars = first.free_variables()
        second_free_vars = second.free_variables()

        quantified_new_first = first
        quantified_new_second = second

        cur_formula = the_new_formula   # (first * second)

        if is_quantifier(first.root):
            print("first is quantifier", formula)
            x = first.variable

            if x in second_free_vars:
                print("x is free in second")
                z = next(fresh_variable_name_generator)
                Rz = first.predicate.substitute({x:Term(z)})     # R(z)
                quantified_new_first = Formula(root, z, Rz)   # Az[R(z)]
                R = Rz.substitute({z: Term('_')})    # R(_)

                equivalent_proof_line = -1
                if root == 'A':
                    equivalent_proof_line = prove_eq_all_rename_var(R, first, Rz, prover, quantified_new_first, x, z) # "Ax[R(x)] <-> Az[R(z)]"
                elif root == 'E':
                    equivalent_proof_line = prove_equ_exist_case(R, Rz, first, prover, quantified_new_first, x, z)

                new_formula = Formula(root, quantified_new_first, quantified_new_second)    # (Az[R(z)] * second)
                origin_formula_eq_new_formula = equivalence_of(formula, new_formula)
                ###################
                step1 = prover.add_tautological_implication(origin_formula_eq_new_formula, {l1, l2, equivalent_proof_line}) # (Ax[R(x)] * second) <-> (Az[R(z)] * second)
                #################
                print("binary done with ", formula)

                cur_formula = new_formula
                first_free_vars = cur_formula.first.free_variables()
                # return new_formula, Proof(assumptions, equivalence_of(formula, new_formula), prover._lines)

            else:
                ##################  simple case    ##############################################
                # if x not in second_free_vars:
                new_and_old_eq = equivalence_of(formula, the_new_formula)
                ########
                step1 = prover.add_tautological_implication(new_and_old_eq, {l1, l2})
                #########
                # return the_new_formula, Proof(assumptions, new_and_old_eq, prover._lines)
                ###################################################################################

        if is_quantifier(second.root):
            print("second is quantifier", formula)

            x = second.variable
            if x in first_free_vars:
                z = next(fresh_variable_name_generator)
                new_second = quantified_new_second.predicate.substitute({x:Term(z)})
                quantified_new_second = Formula(root, z, new_second)   # Az[R(z)]
                R = new_second.substitute({z: Term('_')})    # R(_)

                ll11 = prove_eq_all_rename_var(R, second, new_second, prover, quantified_new_second, x, z) # "Ax[R(x)] <-> Az[R(z)]"

                new_formula = Formula(root, quantified_new_first, quantified_new_second)    # (first * Az[R(z)])
                origin_formula_eq_new_formula = equivalence_of(formula, new_formula)
                ###################
                step1 = prover.add_tautological_implication(origin_formula_eq_new_formula, {l1, l2, ll11}) # (Ax[R(x)] * second) <-> (Az[R(z)] * second)
                #################
                print("binary done with ", formula)

                cur_formula = new_formula
                second_free_vars = cur_formula.second.free_variables()



        new_formula = Formula(root, quantified_new_first, quantified_new_second)
        origin_formula_eq_new_formula = equivalence_of(formula, new_formula)
        print("~~~new formula: ", new_formula)
        #((x<->a)&&(y<->b))->((x&&y)<->(a&&b))
        # (origin_first &|-> origin_second) <-> (first &|-> second)
        eq = equivalence_of(first, quantified_new_first)
        # print("eq", eq)
        # print("eq", origin_formula_eq_new_formula)
        # l533 = prover.add_tautology(eq)
        # l633 = prover.add_tautological_implication(origin_formula_eq_new_formula, {l11})
        print("~~~~~~~~~~binary done with ", formula)
        # print("new formula: ", new_formula)
        # "Ax[R(x)] <-> Az[R(z)]"
        return new_formula, Proof(assumptions, equivalence_of(formula, new_formula), prover._lines)


def prove_equ_exist_case(R, Rz, first, prover, quantified_new_first, x, z):
    """
    proves Ex[R(x)]] <-> Ez[R(z)]
    Returns:

    """
    pred = Formula('->', Rz, first)  # R(z)->Ex[R(x)]
    s1 = prover.add_instantiated_assumption(pred, Prover.EI, {'R': R, 'x': x, 'c': z})  # R(z)->Ex[R(x)]
    form = Formula('A', z, pred)  # Az[R(z)->Ex[R(x)]]
    s2 = prover.add_ug(form, s1)  # Az[R(z)->Ex[R(x)]]
    and_form = Formula('&', form, quantified_new_first)  # Az[R(z)->Ex[R(x)]] & Ez[R(z)]
    imp_form = Formula('->', and_form, first)  # Az[R(z)->Ex[R(x)]] & Ez[R(z)] -> Ex[R(x)]
    s3 = prover.add_instantiated_assumption(imp_form, Prover.ES, {'Q': quantified_new_first, 'R': R,
                                                                  'x': z})  # Az[R(z)->Ex[R(x)]] & Ez[R(z)] -> Ex[R(x)]
    ###
    s4 = prover.add_tautological_implication(Formula('->', quantified_new_first, first),
                                             {s2, s3})  # Ez[R(z)] -> Ex[R(x)]]
    ###
    pred2 = Formula('->', first.predicate, quantified_new_first)  # R(x)->Ez[R(z)]
    s5 = prover.add_instantiated_assumption(pred2, Prover.EI, {'R': R, 'x': z, 'c': x})  # R(x)->Ez[R(z)]
    form2 = Formula('A', x, pred2)  # Ax[R(x)->Ez[R(z)]]
    s6 = prover.add_ug(form, s5)  # Ax[R(x)->Ez[R(z)]]
    and_form2 = Formula('&', form2, first)  # Ax[R(x)->Ez[R(z)]] & Ex[R(x)]
    imp_form2 = Formula('->', and_form2, quantified_new_first)  # Ax[R(x)->Ez[R(z)]] & Ex[R(x)] -> Ez[R(z)]
    s7 = prover.add_instantiated_assumption(imp_form2, Prover.ES,
                                            {'Q': quantified_new_first, 'R': R,
                                             'x': z})  # Ax[R(x)->Ez[R(z)]] & Ex[R(x)] -> Ez[R(z)]
    ###
    s8 = prover.add_tautological_implication(Formula('->', first, quantified_new_first),
                                             {s6, s7})  # Ex[R(x)]] -> Ez[R(z)]
    ###
    l11 = prover.add_tautological_implication(equivalence_of(first, quantified_new_first), {s4, s8}) # Ex[R(x)]] <-> Ez[R(z)]
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
    return Exphi_eq_Expsi


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
    print("quant done with ", formula)
    return Axphi_eq_Axpsi


def create_new_firs_and_second(formula, prover):
    """
    creates the recursivly first and second in the binary case
    """
    first, first_proof = _uniquely_rename_quantified_variables(formula.first)
    l1 = prover.add_proof(first_proof.conclusion, first_proof)  # origin_first <-> first
    # origin_eq_first = equivalence_of(formula.first, first)
    second, second_proof = _uniquely_rename_quantified_variables(formula.second)
    l2 = prover.add_proof(second_proof.conclusion, second_proof)  # origin_second <-> second
    # origin_eq_second = equivalence_of(formula.second, second)
    return first, l1, l2, second


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
