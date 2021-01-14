#!/bin/bash

b1="$(basename -- $1)"
b2="$(basename -- $2)"

# drop comments, collapse file onto a single line, delete
# dictionary and ensure the file ends with a newline
grep -v '//' $1 | tr '\n' ' ' | sed 's/^.*\]//g' | sed -e '$a\' >/tmp/$b1
grep -v '//' $2 | tr '\n' ' ' | sed 's/^.*\]//g' | sed -e '$a\' >/tmp/$b2
diff -b -w /tmp/$b1 /tmp/$b2
