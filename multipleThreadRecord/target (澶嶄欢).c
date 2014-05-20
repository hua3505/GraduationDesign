#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
using namespace std;
int a ;
float b;

void *tprocess1(void *args)
{
    while(1)
    {
        int temp = a;
        temp ++;
        a = temp;
        temp = b;
        temp --;
        b = temp;
        //printf("thread1:a = %d,b = %f\n",a,b);
    }
    return NULL;
}

void *tprocess2(void *args)
{
    while(1)
    {
        int temp = a;
        temp --;
        a = temp;
        temp = b;
        temp ++;
        b = temp;
        //printf("thread2:a = %d,b = %f\n",a,b);
    }
    return NULL;
}

int main()
{

    a = 1;
    b = 2.3;
    int tempA = a;
    float tempB = b;
    printf("a = %d,b = %f\n",tempA,tempB);
    pthread_t t1;
    pthread_t t2;
    pthread_create(&t1,NULL,tprocess1,NULL);
    pthread_create(&t2,NULL,tprocess2,NULL);
    pthread_join(t1,NULL);
    return 0;
}

