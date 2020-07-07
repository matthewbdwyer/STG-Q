#include <stdio.h>

int main()
{
    int a;
    int b;
    scanf("%d", &a);
    scanf("%d", &b);

    int c = 10 + a;
    int d = 10 - b;

    if (c > d) {
        return a;
    }
    else {
        return b;
    }
}