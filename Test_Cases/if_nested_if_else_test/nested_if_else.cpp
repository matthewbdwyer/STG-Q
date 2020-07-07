#include <stdio.h>
#include "../stg_lib/stg.h"

bool isMaxOrMin(int a, int b, int c)
{
    if (a > b) {
        if (a > c) {
            return true;
        }
        else {
            return false;
        }
    }
    else {
        if (b > c) {

            return true;
        }
        else {
            return false;
        }
    }
}

int main()
{
    int a, b, c;

    stg_begin_test();
    stg_symbolic_variable(&a, "X");
    stg_symbolic_variable(&b, "Y");
    stg_symbolic_variable(&c, "Z");
    stg_input_int(&a, 550);
    stg_input_int(&b, 38);
    stg_input_int(&c, 58);
    stg_assert(isMaxOrMin(a, b, c));
    stg_end_test();

    stg_begin_test();
    stg_input_int(&a, 0);
    stg_input_int(&b, 38);
    stg_input_int(&c, 10);
    stg_assert(isMaxOrMin(a, b, c));
    stg_end_test();

    stg_begin_test();
    stg_input_int(&a, 5);
    stg_input_int(&b, 38);
    stg_input_int(&c, 58);
    stg_assert(isMaxOrMin(a, b, c));
    stg_end_test();
}