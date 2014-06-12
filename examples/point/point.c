#include <stdio.h>
#include <string.h>

int g_iA;
int * g_piToGlobal = &g_iA;
int * g_piToLocal;

int g_iArray[10];
int (*g_paToArray)[10] = &g_iArray;
int ** g_pToPoint = &g_piToGlobal;
struct person {
    char name[10];
	int sex;
} yan, * g_pToStruct = &yan;

int main()
{
    int l_iA;
	int l_iB;
	int * l_piToGocal = &g_iA;
	
    // global point to local 
	g_piToLocal = &l_iB;
    *g_piToLocal = 11;
	l_iA = *g_piToLocal;

	// global point to global
	*g_piToGlobal = 12;
	l_iA = *g_piToGlobal;

	// local point to local
    *l_piToGocal = 13;
	l_iA = *l_piToGocal;

    // point to array
    (*g_paToArray)[0] = 1;
	l_iA = (*g_paToArray)[0];

	//point to point
	**g_pToPoint = 2;
	l_iA = **g_pToPoint;

	//point to struct
    strcpy((*g_pToStruct).name, "yan");
	printf("%s", (*g_pToStruct).name);
}
