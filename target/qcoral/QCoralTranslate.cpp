#include <stdlib.h>
#include <iostream>
#include <fstream>

#include "Constraint.h"
#include "QCoralPrinter.h"

using namespace std;

/*! \fn main
   *  \brief The main funtion which calls others for the translation of stg files to qcoral files.
   *
   * \param argc the number arguments given for conversion. 
   * \param argv the pointer array which points to the constraint file (.stg file) and the dictionary file.
*/   

int main(int argc, const char *argv[]) {
  std::ifstream filestream;
  std::istream& stream = (argc == 1) ? cin : filestream;
  if (argc > 1) {
    filestream.open(argv[1]);
  }

  else{
    cout<<"No File location given\n";
    return -1;
  }

  auto constraint = Constraint::parse(stream);

  if (constraint) {

    QCoralPrinter qcp(std::cout, 2);

    // Checking if the argument contains a dictionary file or not. 
    // If it does then use it for conversion otherwise set default params depending on the type of variables inside the stg file.

    if(argc > 2)
      qcp.print(constraint.value(), argv[2]);
    else{
      std::cerr<<"No dictionary file given! Setting default params.\n";
      qcp.print(constraint.value(), NULL);
    }
  } else {
    cout << "STG parse error\n";
  }
}
