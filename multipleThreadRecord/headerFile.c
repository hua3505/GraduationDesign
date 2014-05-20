#include<list>
#include<string.h>
#include <semaphore.h>
using namespace std;

struct variableInfo
{
    int recordSeq;
    int writeOrRead;
    char threadName[16];
    char variableName[8];
};

sem_t bin_sem;
list<struct variableInfo> recordList;
static int recordTime = 1;
int enter_write(char* tName,char *vName);
int enter_read(char* tName,char *vName);

