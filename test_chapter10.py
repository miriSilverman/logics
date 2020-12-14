# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: test_chapter10.py

"""Tests all Chapter 10 tasks."""

from predicates.prover_test import *
from predicates.some_proofs_test import *

def test_skeleton(debug=False):
    test_prover_basic(debug)

def test_task1(debug=False):
    test_add_universal_instantiation(debug)

def test_task2(debug=False):
    test_add_tautological_implication(debug)

def test_task3(debug=False):
    test_add_existential_derivation(debug)

def test_task4(debug=False):
    test_lovers_proof(debug)

def test_task5(debug=False):
    test_homework_proof(debug)

def test_task6(debug=False):
    test_add_flipped_equality(debug)

def test_task7(debug=False):
    test_add_free_instantiation(debug)

def test_task8(debug=False):
    test_add_substituted_equality(debug)

def test_task9(debug=False):
    test_add_chained_equality(debug)

def test_task10(debug=False):
    test_unique_zero_proof(debug)

def test_task11(debug=False):
    test_multiply_zero_proof(debug)

def test_task12(debug=False):
    test_peano_zero_proof(debug)

def test_task13(debug=False):
    test_russell_paradox_proof(debug)


if __name__ == '__main__':

    test_skeleton()
    test_task1()
    test_task2()
    test_task3()
    test_task4()
    test_task5()
    test_task6()
    test_task7()
    test_task8()
    test_task9()
    test_task10()
    test_task11()
    test_task12()
    test_task13()
