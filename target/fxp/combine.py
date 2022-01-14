import os,glob
folder_path = '/tmp/QCounter/fxp'

comb_file = ""
domains = []
declarations = []
combined_assertion = "(assert (or "

for filename in glob.glob(os.path.join(folder_path, '*.fxp')):
  
  file = open(filename, 'r')
  Lines = file.readlines()

  for line in Lines:
  	if "set-info" in line and "domain" in line and line not in domains:
  		domains.append(line)

  	if "declare-fun" in line and line not in declarations:
  		declarations.append(line)

  	if "assert" in line:
  		combined_assertion += line[8:len(line)-2]

combined_assertion += " false))"

print(''.join(domains))
print(''.join(declarations))
print(combined_assertion)