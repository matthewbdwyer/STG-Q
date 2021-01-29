#include <stdio.h>
#include <math.h>
#include <float.h>
#include "stg_lib/stg.h"


bool isIsoscelesRightTriangle(double theta, double hypotenuse)
{
	double height = sin(theta)* sqrt(hypotenuse);
    double base = cos(theta)* sqrt(hypotenuse);

    

	if((height - base) < 0.001){     //	if(fabs(height - base) < 0.001)
        //printf("%lf\n",height );
        //printf("%lf\n",base );
		return true;
    }
	else return false;
}

int main()
{
    double theta, hyp_sqr; // theta in degree // hyp_sqr =  square of hypotenuse
    stg_symbolic_variable(&theta, "T", DBL_MIN, DBL_MAX);
    stg_symbolic_variable(&hyp_sqr, "H", DBL_MIN, DBL_MAX);

    stg_begin_test();
    scanf("%lf",&theta);
    theta = theta* M_PI/180; // converting from degree to radian
    scanf("%lf",&hyp_sqr);
    bool is_isosceles = isIsoscelesRightTriangle(theta,hyp_sqr);
    stg_end_test();

    stg_record_test(is_isosceles);
    print_maps();
    return 0;
}