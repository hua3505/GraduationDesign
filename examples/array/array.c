#include <stdlib.h>

int score[10];

struct person
{
    char name[10];
	int sex;
} pepole[10];

int (* g_apScore[4])[10];

int main()
{
    score[0] = 1;
	pepole[0].sex = 0;
	g_apScore[0] = &score;
	return 0;
}
