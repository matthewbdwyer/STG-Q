import sys
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO # Py2-Py3 Compatibility
from pysmt.shortcuts import get_model
import time

BV = True
if BV:
    from pysmt.rewritings import get_fp_bv_converter
else:
    from pysmt.rewritings import get_fp_real_converter

with open(sys.argv[1], 'r') as f:
    QUERY=f.read()

# We read the SMT-LIB Script by creating a Parser.
# From here we can get the SMT-LIB script.
parser = SmtLibParser()

# The method SmtLibParser.get_script takes a buffer in input. We use
# cStringIO to simulate an open file.
# See SmtLibParser.get_script_fname() if to pass the path of a file.
script = parser.get_script(cStringIO(QUERY))

# The SmtLibScript provides an iterable representation of the commands
# that are present in the SMT-LIB file.
#
# Printing a summary of the issued commands
f = script.get_last_formula()

if BV:
    conv = get_fp_bv_converter()
else:
    conv = get_fp_real_converter()

F = conv.convert(f)

if BV:
    print("(set-logic QF_UFBV)")
else:
    print("(set-logic QF_NIRA)")

for line in QUERY.splitlines():
  if "set-info" in line and "domain" in line:
      print(line.replace("UniformReal", "UniformInt"))

sm = conv.symbol_map
inv_sm = {v:k for k, v in sm.items()}

for old_n, new_n in conv.symbol_map.items():
    print("(declare-fun {} {})".format(old_n.to_smtlib(), new_n._content.payload[1].as_smtlib(funstyle=True)))

for x in F.get_free_variables():
    if x in inv_sm.keys():
        old_n = inv_sm[x]
        print("(define-fun {} {} {})".format(x.to_smtlib(), x.get_type().as_smtlib(), old_n.to_smtlib()))
    else:
        print("(declare-fun {} {})".format(x.to_smtlib(), x._content.payload[1].as_smtlib(funstyle=True)))
print("(assert {})".format(F.to_smtlib()))
print("(check-sat)")

