# Testing for STG library
The directory `inputs` contains a set of `.stg` files.

The script `run.sh` runs the STG constraint driver on each file.  This exercises the parser, constraint builder, constraint IR, and constraint printer.

The driver produces a pretty printed version of the original constraint that may differ in terms of white-space, comments, ordering of dictionary elements, and printed resolution of floating point constants.  The script eliminates white-space and comment differences, but the others are more complicated to address.  While they are not completely eliminated the nature of the differences is localized to permit easy inspection of the differences.

The script leaves a file `.stg.out` in the `inputs` directory for further inspection.
