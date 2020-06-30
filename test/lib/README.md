# Testing for STG library
The directory `parsetype-inputs` contains two set of `.stg` files in the `pass` and `fail` directories.

The script `run.sh` runs the STG pretty printer, `stgpp`, with constant folding disabled, `-no-constant-folding` on each file.  This exercises the parser, constraint builder, constraint IR, constraint type checker, and constraint printer.

The driver produces a pretty printed version of the original constraint that may differ in terms of white-space, comments, ordering of dictionary elements, and printed resolution of floating point constants.  The script eliminates white-space and comment differences, but the others are more complicated to address.  While they are not completely eliminated the nature of the differences is localized to permit easy inspection of the differences.

For tests that are expected to fail, the output of `stgpp` is expected to include the string `error`, as in `STG parse error` or `STG type error`.

The script leaves a file `.stg.out` in the `parsertype-inputs/*` directories for further inspection.

The script returns `pass` if all tests pass and `fail`, with additional details, otherwise.

