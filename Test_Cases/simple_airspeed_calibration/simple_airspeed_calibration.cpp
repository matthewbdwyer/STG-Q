/*
 ** Simpler version of calibration airspeed from
 **   https://github.com/PX4/Firmware/blob/master/src/modules/commander/airspeed_calibration.cpp
 ** Removed libraries
 ** Removed orb oub/sub and used method parameters instead
 ** Removed pointers
 ** Removed some other pressure parameters and checks
 ** Note that:
 **    I left floats in this one (we could replace them with ints if floats are not yet supported)
 **    We are reading several inputs as part of a stream in the single readAir function
 */

#include <stdio.h>
#include "../stg_lib/stg.h"
#define maxcount 5

float readAir[maxcount];

bool do_airspeed_calibration(float analog_scaling)
{
    int successfulCalibration = 0;
    int calibration_counter = 0;
    int calibration_count = (maxcount * 2) / 3;

    /* only warn if analog scaling is zero */

    if (analog_scaling < 0.1 && analog_scaling > -0.1) {
        // No airspeed sensor found
        successfulCalibration = 0;
    }
    else {
        float diff_pres_filtered_pa;

        /* Take a few samples and make sure pitot tubes are not reversed,  */

        while (calibration_counter < maxcount) {

            printf("calibration_counter %d\n", calibration_counter);

            diff_pres_filtered_pa = readAir[calibration_counter];

            if (diff_pres_filtered_pa > 50) {
                // Positive pressure: OK
                successfulCalibration = 1;
                break;
            }

            if (diff_pres_filtered_pa < 0) {
                /* do not allow negative values */
                successfulCalibration = 0;
                break;
            }

            calibration_counter++;
        }
    }

    // Many iterations without reaching at least a 50 reading...
    if (calibration_counter == maxcount) {
        successfulCalibration = 0;
    }
    printf("retun value %d\n", successfulCalibration);

    return successfulCalibration;
}

int main()
{

    /* Symbolic analog_scaling, and readAir[] */
    /* TODO Add                               */
    /*    stgset symbolic analog_scaling(...) */
    /*    stgset symbolic readAir[10]         */

    float valueArray[5] = { 20.3, 4.5, 8.7, 8.0, 8.2 };
    float valueArray1[5] = { 20.3, 4.5, 50.7, 8.0, 8.2 };

    stg_begin_test();
    stg_symbolic_array(readAir, "float", 5, "S");
    stg_input_array(readAir, "float", 5, valueArray);
    stg_assert(do_airspeed_calibration(1.0));
    stg_end_test();

    stg_begin_test();
    stg_symbolic_array(readAir, "float", 5, "S");
    stg_input_array(readAir, "float", 5, valueArray1);
    stg_assert(do_airspeed_calibration(1.0));
    stg_end_test();


}