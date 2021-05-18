#include <stdlib.h>
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "SMTPrinter.h"

using namespace std;

/*! \fn main
   *  \brief The main funtion which calls others for the translation of stg files to smt2 files (int/reals).
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
    cout<<"SMTPrinter takes 2 arguments. File_location & Dictionary_loc \n";
    return -1;
  }

  auto constraint = Constraint::parse(stream);

  if (constraint) {
    // cout << "STG parsesd successfully\n";
    SMTPrinter smtp(std::cout, 2);
    smtp.print(constraint.value(), argv[2]);
  } else {
    cout << "STG parse error\n";
  }
}
