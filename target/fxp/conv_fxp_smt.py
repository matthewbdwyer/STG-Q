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
	# print(line)
	if "set-info" in line and "domain" in line:

		var_ind = line.index("domain") + 8
		space_ind = line.index(" ", var_ind)
		new_command = line[:var_ind] + "FV" + str(i) + line[space_ind:]
		
		print(new_command)
		i += 1

for x in F.get_free_variables():
    print("(declare-fun {} {})".format(x.to_smtlib(), x._content.payload[1].as_smtlib(funstyle=True)))

print("(assert {})".format(F.to_smtlib()))
print("(check-sat)")