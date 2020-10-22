# This file is part of the materials accompanying the book 
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2020
# File name: test_chapter01.py

"""Tests all Chapter 1 tasks."""

from propositions.syntax_test import *

def test_task1(debug=False):
    test_repr(debug)

def test_task2(debug=False):
    test_variables(debug)

def test_task3(debug=False):
    test_operators(debug)

def test_task4(debug=False):
    test_parse_prefix(debug)

def test_task5(debug=False):
    test_is_formula(debug)

def test_task6(debug=False):
    test_parse(debug)

def test_task7(debug=False):
    test_polish()

# def test_task8(debug=False):
#     test_parse_polish()

test_task1()
test_task2()
test_task3()
test_task4()
test_task5()
test_task6()
test_task7(True) # Optional
#test_task8(True) # Optional
