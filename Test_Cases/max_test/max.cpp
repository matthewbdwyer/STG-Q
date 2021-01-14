#include <stdio.h>
#include "../stg_lib/stg.h"


int find_max(int a, int b)
{
   if (a > b) {
      return a;
   }
   else 
   {
      return b;
   }
}

int main()
{
   int a;
   int b;
   stg_begin_test();
   stg_symbolic_variable(&a, "A");
   stg_symbolic_variable(&b, "B");
   stg_input_int(&a, 38);
   stg_input_int(&b, 78);
   find_max(a,b);
   stg_assert(true);
   stg_end_test();
   return 0;
}
