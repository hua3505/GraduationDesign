#include <iostream>

int a;
int ai;
float b;
char str[10];
int * pi;

void f1()
{
    std::cout << *pi << std::endl;
	*pi = 542;
}

int main()
{
    char c;
	str[1] = 'h';
    c = str[1];
	pi = &a;
	ai = a;
	pi = new int(10);
    *pi = 100;
	*pi = 234;
	f1();
    return 0;
}
