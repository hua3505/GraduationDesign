#include <stdlib.h>

char * g_str;
int g_iTest;
int * g_pi;

int main()
{
    char * l_str;
	char c;
	char cc;
	char * l_c = &c;
	int * l_pi = &g_iTest;

	l_str = malloc(10 * sizeof(char));
	l_str[0] = '1';
	c = l_str[0];
	g_str = l_str;
	g_str[1] = 'g';
	c = g_str[1];
    *l_c = 'c';
    cc = *l_c;
	g_str = l_c;
	*g_str = 'g';

	//
	g_pi = l_pi;
	*g_pi = 9;
	*l_pi = 10;

}
