
# Combining multiple smt2 files into a single file for quantification.

import os,glob
folder_path = '/tmp/QCounter/smt'

comb_file = ""
domains = []
declarations = []
exp_assert = ""
combined_assertion = "(assert (or "

for filename in glob.glob(os.path.join(folder_path, '*.smt')):
  
  file = open(filename, 'r')
  Lines = file.readlines()

  for line in Lines:
  	if "set-info" in line and "domain" in line and line not in domains:
  		domains.append(line)

  	if ("declare-const" in line or "declare-fun" in line) and line not in declarations:
  		declarations.append(line)

  	if "assert" in line and "EXP" not in line:
  		combined_assertion += line[8:len(line)-2]

  	if "EXP" in line:
  		exp_assert = line

combined_assertion += " false))"

print(''.join(domains))
print(''.join(declarations))
print(exp_assert)
print(combined_assertion)
