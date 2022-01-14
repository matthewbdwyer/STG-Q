#include <stdlib.h>
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "FXPPrinter.h"

using namespace std;

int main(int argc, const char *argv[]) {
  std::ifstream filestream;
  std::istream& stream = (argc == 1) ? cin : filestream;
  if (argc > 2) {
    filestream.open(argv[1]);
  }

  else{
    cout<<"FXPPrinter takes 2 arguments. File_location & Dictionary_loc \n";
    return -1;
  }

  auto constraint = Constraint::parse(stream);

  if (constraint) {
    // cout << "STG parsesd successfully\n";
    FXPPrinter fxpp(std::cout, 2);
    fxpp.print(constraint.value(), argv[2]);
  } else {
    cout << "STG parse error\n";
  }
}
