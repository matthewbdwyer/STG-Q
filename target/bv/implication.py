from z3 import *
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("file1")
parser.add_argument("file2")
args = parser.parse_args()

file1 = open(args.file1, 'r')
smt_input1 = file1.read().replace("\n", " ")
file1.close()

file2 = open(args.file2, 'r')
smt_input2 = file2.read().replace("\n", " ")
file2.close()

assertion1 = parse_smt2_string(smt_input1)
assertion2 = parse_smt2_string(smt_input2)

formula1 = And(assertion1)
formula2 = And(assertion2)

prove(Implies(formula1, formula2))
prove(Implies(formula2, formula1))

