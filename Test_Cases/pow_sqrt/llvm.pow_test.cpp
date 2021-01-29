#include <stdio.h>
#include <math.h>
#include <float.h>
#include "stg_lib/stg.h"


bool isGreaterThan(double x, double y)
{
    double result;
    if( pow(x,y)>pow(x,2))
        result=pow(x,y);
    else result=pow(x,2);
    
    if(pow(x,y)>0.5 ) return true;
    else return false;
}



int main()
{
    double base; double power;
    stg_symbolic_variable(&base, "B", DBL_MIN, DBL_MAX);
    stg_symbolic_variable(&power, "P", FLT_MIN, FLT_MAX); 

    stg_begin_test();
    scanf("%lf",&base);
    scanf("%lf",&power);
    bool result=isGreaterThan(base,power);
    stg_end_test();

    stg_record_test(result);
    //print_maps();
    return 0;
}