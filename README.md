# STG-Q

This repository supports the quantification of STG constraints.  It consists of a library for manipulating constraints generated by the STG instrumentation component [STG-I](https://github.com/soneyahossain/STG-I), tools for simplifying constraints, translators for target quantification tools, and tools for aggregating quantification results.

## STG constraints
STG constraints are defined by a [grammar](ConstraintGrammar.g4) written in [ANTLR4](https://www.antlr.org/).  A constraint consists of a dictionary which defines set of symbol definitions (a name, type, and initial value) and a boolean expression written in terms of symbols, constants, and the operators defined by the grammar.

Operators in STG constraints are designed to reflect those that are implemented in LLVM [instructions](https://llvm.org/docs/LangRef.html#instruction-reference) and [comparisons](https://llvm.org/docs/LangRef.html#icmp-instruction).  Only the operators that are applied to values computed in terms of program inputs are supported.  For example, pointer manipulating instructions such as [GEP](https://llvm.org/docs/LangRef.html#icmp-instruction) are not supported since they operate on *addresses* to which values are stored and not the values themselves.  More generally, operators manipulating [l-values](https://en.wikipedia.org/wiki/Value_(computer_science)#lrvalue) are not be supported.

The constraint `[ S0:i32 = 7 ] (slt S0 (i32 10))` expresses that a signed 32-bit Integer symbol, `S0`, is less than 10.  Additional constraint examples are in the [test](test/lib/inputs/pass) sub-directories.  By convention we use  an `.stg` suffix for files with the textual encoding of an STG constraint.

## Building the library associated executables
The library is implemented in C++ using an ANTLR4 generated lexer, parser, and parse-tree [visitor](https://en.wikipedia.org/wiki/Visitor_pattern).

This project uses `cmake` to manage the build process.  The `CMakeLists.txt` file configures the ANTLR4 and Cpp build process, e.g., source files, targets, libraries, etc.   The file requires 3.13 of `cmake`. 

We follow the `cmake` build model for the [ANTLR4 Cpp target](https://github.com/antlr/antlr4/tree/master/runtime/Cpp/cmake).  The `cmake` directory stores ANTLR4 related cmake files.

You will need to adjust the path to the jar file that ANTLR4 uses (`antlr-4.8-complete.jar`) which is hardcoded in `CMakeLists.txt`.   Note that if the normal install of `antlr4` doesn't provide you with this file, then you can download it from the [ANTLR4 download site](https://www.antlr.org/download/antlr-4.8-complete.jar) and place it wherever you like, e.g., `$HOME/lib`, and then point to it from `CMakeLists.txt`.

You need to create a `build` directory within which you will build the library.  To get started you should create that, empty, build directory if it doesn't exist.  All of the generated runtime files for ANTLR4 will be built the first time and stored in the build directory; this may take some time.

To build the libraries and executable:
  1. `mkdir build`
  2. `cd build`
  3. `cmake ../src`
  4. `make`

NB: You may see warnings related to ignored type attribute ATN that are due to some
type gymnastics in the current implementation of the ANTLR4 CPP Visitor implementation.

This will produce two executables:
- `build/stgpp` : takes the name of a `.stg` file, parses it, and pretty print its contents to stdout.
- `build/stg2qc` : takes the name of an `.stg` file, parses it, and prints the constraint in a form that can be accepted by the `qCoral` counter.

## Repository and library structure and components
The [include](include) directory stores the header files needed by translators and other constraint manipulating tools.  The library [source](source/lib) has the source code for the library components including the grammar file, `ConstraintGrammar.g4`.   Generating a parser from this file produces a number of ANTLR4 generated files.  These are not under configuration management and are stored in the `build` directory once generated.

`Constraint.{h,cpp}` define the core data structure.  The core type is
`Constraint::Constraint` which stored the dictionary information and
an constraint expression.  Constraint expressions are instances of
subtypes of `Constraint::Expr`, the base class, and generally are
constituted by a tree of such expressions.  To reduce duplication
of symbols, `Constraint::Symbol`, in expressions their definitions
are interned.  Arbitrary expressions could be interned since they
are side-effect free, but this has not been implemented.

`ConstraintBuilder.{h,cpp}` implements a subtype of an ANTLR4 parse-tree
visitor.  It traverses the parse-tree and constructs an instance of 
`Constraint::DictExpr`.

Once built a `Constraint::Constraint` structure can be processed by 
subtyping `ConstraintVisitor`, defined in `ConstraintVisitor.h`. 
`ConstraintPrinter.{h,cpp}` is one such visitor that pretty prints 
a constraint.  `QCoralPrinter.{h.cpp}` for the [qcoral](target/qcoral) target
is another example of a constraint visitor.

## STG Tools
There are several scripts that are useful for simplifying sets of constraints.
`src/tools/stgred.sh` accepts the name of a directory and prints the names of redundant `.stg` files.  It does this by performing some preprocessing, e.g., dropping the dictionary, and then diffing the constraints; implemented in `src/tools/stgdiff.sh`.

These tools should be installed in a directory and the shell variable `STGINSTALL` should be set to that directory's path.  This is how these STG scripting tools reference one another.

## Testing
Tests for the library itself are run using the script `run.sh` in [test/lib](tests/lib).
There are 6 test inputs which cover all of the STG operators and many of their combinations; the grammar is rather simple so this ends up being a decent initial test suite.  There are also tests which are expected to produce parse errors.  

Each target is expected to provide its own `run.sh` script to test its translator and associated tools.

## Translating Constraints for Targets
We know that there will not be a direct one-to-one mapping
from STG constraint operators and types into the input languages of all targets.

There are several strategies that we can use to address this:
- throw an `Unsupported` assertion (this is the minimal behavior)
- rewrite an operator into an *equivalent* expression
- rewrite an operator into an underapproximating expression
- rewrite an operator into an overapproximating expression

For the last two cases, translators should record a series of log
messages, e.g., in comments embedded into the translated constraint, 
documenting the approximations.  Downstream tools might consume these
to provide information about the fidelity of any computed results from
the translated expressions.


## Improvement and Extensions

### Type Checking
It would be nice to build a simple type checking pass using the visitor.
It would also allow us to perform type checking after constraint transformation.

### Constraint Transformation
Build a constant folding transformation.

## qCORAL target :

### Requirements

  1. RealPaver
      - Download RealPaver: http://pagesperso.lina.univ-nantes.fr/~granvilliers-l/realpaver/src/realpaver-0.4.tar.gz
      - Run "tar -xzvf realpaver-0.4.tar.gz"
      - Inside the extracted directory: Run "./configure; make"
  2. Java 1.7+
  3. Ant (we use 1.9)
  
### Installation

1. Download qCORAL: https://s3-us-west-2.amazonaws.com/qcoral/qcoral-fse-replication.tar.xz
2. Uncompress the file
3. Set the location of the RealPaver executable in "scripts/variables" (Eg. => ....../realpaver-0.4/bin/realpaver)
4. After this, if you can have a constraint file (.qcoral file), you can run the following command to generate the probability distribution.

   ./run_qcoral --mcIterativeImprovement --mcProportionalBoxSampleAllocation \
   --mcSeed 123456 --mcMaxSamples 500000 --mcInitialPartitionBudget 50000 \
   --mcTargetVariance 1E-20 --mcSamplesPerIncrement 10000 \
   your_file.qcoral
   
### qCORAL documentation

To know more about the command line arguments: http://qcoral.s3-website-us-west-2.amazonaws.com/QCoralOptions.html

To know more about qCORAL: http://qcoral.s3-website-us-west-2.amazonaws.com/index.html

