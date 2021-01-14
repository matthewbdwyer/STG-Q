# Testing for STG tools
The directory `duplicated-inputs` contains subdirectories with sets of `.stg` files.  For each such directory an additional file, with the suffix `.out`, has the names of duplicated constraints.

The script `run.sh` runs the STG duplicate checker, `stgred.sh`, on each such directory.  This normalizes the textual structure of the constraints and performs a textual diff to detect whether any are duplicates.  This only detects syntactic duplicates.  These are the type we expect to arise due to multiple inputs being executed by `STG-I` that take the same branch sequence.

The directory `fold-inputs` contains a set of `.stg` files that are designed to exercise the constraint folder.  In particular all of these files should simplify to "true", which is encoded as the STG constraint `(i1 1)`.

The script `run.sh` runs the STG pretty printer with the constant folder enabled on each file and compares its output to `(i1 1)`.

The script returns `pass` if all tests pass and `fail`, with additional details, otherwise.

