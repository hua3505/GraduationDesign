#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
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

using namespace std;
int a ;
float b;

void *tprocess1(void *args)
{
    while(1)
    {
enter_read("tprocess1","a");
        int temp = a;
        temp ++;
enter_write("tprocess1","a");
        a = temp;
enter_read("tprocess1","b");
        temp = b;
        temp --;
enter_write("tprocess1","b");
        b = temp;
        //printf("thread1:a = %d,b = %f\n",a,b);
    }
    return NULL;
}

void *tprocess2(void *args)
{
    while(1)
    {
enter_read("tprocess2","a");
        int temp = a;
        temp --;
enter_write("tprocess2","a");
        a = temp;
enter_read("tprocess2","b");
        temp = b;
        temp ++;
enter_write("tprocess2","b");
        b = temp;
        //printf("thread2:a = %d,b = %f\n",a,b);
    }
    return NULL;
}

int main()
{
    int res = sem_init(&bin_sem, 0, 1);
    if (res != 0)
    {
         printf("Semaphore initialization failed\n");
    }


enter_write("main","a");
    a = 1;
enter_write("main","b");
    b = 2.3;
enter_read("main","a");
    int tempA = a;
enter_read("main","b");
    float tempB = b;
    printf("a = %d,b = %f\n",tempA,tempB);
    pthread_t t1;
    pthread_t t2;
    pthread_create(&t1,NULL,tprocess1,NULL);
    pthread_create(&t2,NULL,tprocess2,NULL);
    pthread_join(t1,NULL);
    
    list<struct variableInfo>::iterator itor;
    itor=recordList.begin();
    FILE *file = fopen("result.txt","w");
    if(file == NULL)
    {
        printf("open file error!\n");
        return -1;
    }
    
    while(itor!=recordList.end())
    {
        fprintf(file,"%s %s %s %d\n",itor->threadName,itor->variableName,(itor->writeOrRead?"write":"read"),itor->recordSeq);
        //cout<< itor->threadName<<endl;
        //cout<< itor->variableName<<endl;
        //cout<< itor->recordSeq<<endl;
        //cout<< itor->writeOrRead<<endl;
        itor++;
    }
    fclose(file);
    sem_destroy(&bin_sem);

    return 0;
}

int enter_write(char* tName,char *vName)
{
    sem_wait(&bin_sem);
    struct variableInfo vInfo;
    strcpy(vInfo.threadName,tName);
    strcpy(vInfo.variableName,vName);
    vInfo.recordSeq = recordTime;
    vInfo.writeOrRead = 1;
    recordList.push_back(vInfo);
    printf("thread:%s,variable:%s,option:write,time:%d\n",tName,vName,recordTime);
    recordTime ++;
    sem_post(&bin_sem);
    return 0;
}

int enter_read(char* tName,char *vName)
{
    sem_wait(&bin_sem);
    struct variableInfo vInfo;
    strcpy(vInfo.threadName,tName);
    strcpy(vInfo.variableName,vName);
    vInfo.recordSeq = recordTime;
    vInfo.writeOrRead = 0;
    recordList.push_back(vInfo);
    printf("thread:%s,variable:%s,option:read,time:%d\n",tName,vName,recordTime);
    recordTime ++;
    sem_post(&bin_sem);
    return 0;
}
