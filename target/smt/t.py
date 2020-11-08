from z3 import *

# smt_input = '''\
# (declare-const EXP Real)
# (assert (= EXP 2.71828182846))
# (declare-const id_1 Int)
# (assert (>= id_1 -100000))
# (assert (<= id_1 100000))
# (declare-const id_2 Int)
# (assert (>= id_2 -100000))
# (assert (<= id_2 100000))
# (assert (>= id_1 id_2))'''
# (assert (and (not (= id_1 id_2)) (= id_1 id_2)))

# smt_input = '''(declare-const EXP Real)
# (assert (= EXP 2.71828182846))(declare-const id_1 Int)
# (assert (>= id_1 -100000 ))(assert (<= id_1 100000 ))
# (declare-const id_2 Int)
# (assert (>= id_2 -100000 ))(assert (<= id_2 100000 ))

# (assert (> (+ 10 id_1) (- 10 id_2)))'''

smt_input1 = '''
(declare-const id_1 Int) (assert (>= id_1 -20 ))(assert (<= id_1 20 )) (declare-const id_2 Int) (assert (>= id_2 -20 ))(assert (<= id_2 20 )) (declare-const id_3 Int) (assert (>= id_3 -20 ))(assert (<= id_3 20 ))
(assert (and (not (<= id_1 0)) (and (not (<= id_2 0)) (and (not (<= id_3 0)) (and (= id_1 id_2) (and (= id_1 id_3) (= id_2 id_3)))))))'''


smt_input2 = '''
(declare-const id_1 Int)
(assert (>= id_1 -20 ))(assert (<= id_1 20 ))
(declare-const id_2 Int)
(assert (>= id_2 -20 ))(assert (<= id_2 20 ))
(declare-const id_3 Int)
(assert (>= id_3 -20 ))(assert (<= id_3 20 ))

(assert (and (not (or (or (< id_1 1) (< id_2 100)) (< id_3 1))) (and (= id_1 id_3) (= id_2 id_3))))'''


# smt_input1 = '''
# (declare-const id_1 Int) (assert (>= id_1 0))'''


# smt_input2 = '''
# (declare-const id_1 Int) (assert (>= id_1 1))'''


# assertions = parse_smt2_string(smt_input)

# formula = And(assertions)
# print(formula)

# solver = Solver()
# solver.add(formula)
# result = solver.check()

# if(result == sat):
# 	print(solver.model())  
# else:
# 	print(result)

assertion1 = parse_smt2_string(smt_input1)
assertion2 = parse_smt2_string(smt_input2)

formula1 = And(assertion1)
formula2 = And(assertion2)

prove(Implies(formula2, formula1))


