#include <stdio.h>
#include <math.h>
#include <float.h>
#include "stg_lib/stg.h"


bool isGreaterThan(double x, float y)
{
    if( (log(x)+y)>(log10(y)+x))
        return true;
    else return false;
}



int main()
{
    double x; float y;
    stg_symbolic_variable(&x, "log_x", DBL_MIN, DBL_MAX);
    stg_symbolic_variable(&y, "log_y", FLT_MIN, FLT_MAX); 

    stg_begin_test();
    scanf("%lf",&x);
    scanf("%f",&y);
    bool result=isGreaterThan(x,y);
    stg_end_test();

    stg_record_test(result);
    //print_maps();
    return 0;
}