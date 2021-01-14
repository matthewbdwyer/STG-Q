#include <stdio.h>
int main()
{
    int num1, num2, num3, min;
    printf("Input the value of var1:");
    scanf("%d", &num1);
    printf("Input the value of var2:");
    scanf("%d",&num2);

    printf("Input the value of var2:");
    scanf("%d",&num3);
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
    printf("Among %d, %d, %d minimum number is %d",num1,num2,num3,min);
    return min;
}
