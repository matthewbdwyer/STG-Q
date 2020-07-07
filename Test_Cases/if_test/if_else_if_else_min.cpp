#include <stdio.h>
#include "../stg_lib/stg.h"

int find_min(int num1, int num2, int num3)
{
    int min;
    if(num1<num2)
    {
       if(num1<num3)
         min = num1;
       else
         min = num3;
    }
    else
    {
       if(num2<num3)
         min = num2;
       else
        min = num3;
    }
    printf("among %d, %d, %d ,  minimum number is: %d",num1,num2,num3,min);
    return min;
}

int main()
{
   int a,b,c;
   stg_begin_test();
   stg_symbolic_variable(&a, "A");
   stg_symbolic_variable(&b, "B");
   stg_symbolic_variable(&c, "C");
   stg_input_int(&a, 38);
   stg_input_int(&b, 78);
   stg_input_int(&c, 78);
   find_min(a,b,c);
   stg_assert(true);
   stg_end_test();

   stg_begin_test();
   stg_input_int(&a, 1);
   stg_input_int(&b, 4);
   stg_input_int(&c, 3);
   find_min(a,b,c);
   stg_assert(true);
   stg_end_test();

   stg_begin_test();
   stg_input_int(&a, 1);
   stg_input_int(&b, 1);
   stg_input_int(&c, 1);
   find_min(a,b,c);
   stg_assert(true);
   stg_end_test();

   return 0;
}

