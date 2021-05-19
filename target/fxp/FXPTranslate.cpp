#include <stdlib.h>
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "FXPPrinter.h"

using namespace std;

/*! \fn main
   *  \brief The main funtion which calls others for the translation of stg files to fixed point smt files.
   *
   * \param argc the number arguments given for conversion. 
   * \param argv the pointer array which points to the constraint file (.stg file) and the dictionary file.
*/ 

int main(int argc, const char *argv[]) {
  std::ifstream filestream;
  std::istream& stream = (argc == 1) ? cin : filestream;

  if (argc > 2) {
    filestream.open(argv[1]);
  }

  else{
    cout<<"FXPPrinter takes 2 arguments minimum. File_location & Dictionary_loc \n";
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
