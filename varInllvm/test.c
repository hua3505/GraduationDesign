#include <stdlib.h>

int iA;
char cA;
double lfA;
int * ipB;
int iaB[5];

struct test{
    int _a;
	char _b;
} testC;

int main()
{
    int * ipC;
	iA = 1;
	cA = 'c';
	lfA = 2.1;
	ipB = &iA;
	iaB[0] = 1;
    testC._a = 1;
	testC._b = 'b';
    ipB = (int *)malloc(4);
	ipC = ipB;
    *ipB = 2;
	*ipB = 3;
	return 0;
}
