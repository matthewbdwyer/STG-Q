import sys

from pysmt.typing import SFXPType, SFXPType, FXP_OM, FXP_RM
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO
from pysmt.shortcuts import *
from pysmt.rewritings import get_fp_real_converter, get_fp_bv_converter
from pysmt.operators import *


conv =  get_fp_bv_converter()
# conv = get_fp_real_converter()

with open(sys.argv[1], 'r') as f:
    QUERY=f.read()

parser = SmtLibParser()

script = parser.get_script(cStringIO(QUERY))
f = script.get_last_formula()
F = conv.convert(f)

i = 0

for line in QUERY.splitlines():
	if "set-info" in line and "domain" in line:
		print(line.replace("UniformReal", "UniformInt"))


sm = conv.symbol_map
inv_sm = {v:k for k, v in sm.items()}

for old_n, new_n in conv.symbol_map.items():
    print("(declare-fun {} {})".format(old_n.to_smtlib(), new_n._content.payload[1].as_smtlib(funstyle=True)))

for x in F.get_free_variables():
    if x not in inv_sm.keys():
        print("(declare-fun {} {})".format(x.to_smtlib(), x._content.payload[1].as_smtlib(funstyle=True)))


final_formula = F.to_smtlib()

for x in F.get_free_variables():
    if x in inv_sm.keys():
        old_n = inv_sm[x]
        final_formula = final_formula.replace(x.to_smtlib(), old_n.to_smtlib())


print("(assert ", final_formula, ")")
print("(check-sat)")