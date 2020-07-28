#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <optional>

#include "Constraint.h"
#include "ConstraintPrinter.h"
#include "ConstraintTypeChecker.h"
#include "ConstraintFolder.h"

#include "llvm/Support/CommandLine.h"

using namespace std;
using namespace llvm;

static cl::OptionCategory
    STGPPcat("stgpp Options",
             "Options for controlling STG constraint pretty printing.");
static cl::opt<bool> notc("no-type-checking", 
                        cl::desc("disable type checking"), 
                        cl::cat(STGPPcat));
static cl::opt<bool> nocf("no-constant-folding", 
                        cl::desc("disable constant folding"), 
                        cl::cat(STGPPcat));
static cl::opt<bool> verbose("verbose", 
                        cl::desc("verbose mode"), 
                        cl::cat(STGPPcat));
static cl::opt<std::string> sourceFile(cl::Positional,
                                       cl::desc("<stg source file>"),
                                       cl::Required, cl::cat(STGPPcat));

int main(int argc, const char *argv[]) {
  cl::HideUnrelatedOptions(STGPPcat); // suppress non STGPP options
  cl::ParseCommandLineOptions(argc, argv, "stgpp - STG constraint pretty printer with type checking and constant folding\n");

  std::ifstream stream;
  stream.open(sourceFile);

  if (auto maybeConstraint = Constraint::parse(stream)) {
    auto constraint = maybeConstraint.value();

    if (!notc) {
      if (verbose) cerr << "STG type checking\n";
      ConstraintTypeChecker ctc;
      if (!ctc.check(constraint, verbose)) {
        cout << "STG type error\n";
        exit (EXIT_FAILURE);
      }
    }

    if (nocf) {
      if (verbose) cerr << "STG constant folding\n";
      ConstraintFolder cf;
      cf.fold(constraint, verbose);
    }

    ConstraintPrinter cp(std::cout, 2);
    cp.print(constraint);
  } else {
    cout << "STG parse error\n";
    exit (EXIT_FAILURE);
  }

}
