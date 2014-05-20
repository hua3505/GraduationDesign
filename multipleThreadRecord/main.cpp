#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

using namespace std;

#define INFO_FILE "info.txt"
#define TARGET_FILE "target.c"
#define TEMP_FILE "temp.c"
#define RECORD_FILE "recordModule.c"
#define HEADER_FILE "headerFile.c"
#define RECORDTO_FILE "recordToFile.c"
#define SEMINIT_FILE "semInit.c"

//存储变量信息的结构体
struct variableInfomation
{
    int lineNumber;
    int writeOrRead;
    char threadName[16];
    char variableName[8];
};

/**
获取变量的操作次数
param：FILE * pfile  要读取的文件的指针
return: 0 成功
**/
int getLinesOfFile(FILE * pfile);

/**
把变量操作替换为模块入口,并在函数头插入声明，在函数尾插入记录模块
param：struct variableInfomation *variableInfo 存储变量信息的结构体数组
param：int lines 数组的大小
return: 0 成功
**/
int replaceActions( struct variableInfomation *variableInfo,int lines);


int main()
{
    //打开文件部分
    FILE *pInfo = NULL;
    pInfo = fopen(INFO_FILE,"r+");
    if(pInfo == NULL)
    {
        printf("open file failed\n");
        return -1;
    }

    //获取变量操作的次数
    int lines = getLinesOfFile(pInfo);
    //printf("lines of file = %d\n",lines);
    //根据变量操作的次数，创建变量信息的结构体数组
    struct variableInfomation variableInfoArray[lines];

    fseek( pInfo, 0, SEEK_SET );                    //把指针移到文件头

    //对结构体进行赋值
    int index = 0;
    while( !feof(pInfo))
    {
        fscanf(pInfo,"%d %d %s %s",&variableInfoArray[index].lineNumber,&variableInfoArray[index].writeOrRead,variableInfoArray[index].threadName,variableInfoArray[index].variableName);
        index ++;
    }
    replaceActions(variableInfoArray,lines);
    for(index = 0;index < lines;index ++)
    {
        printf("lines = %d,writeOrRead = %d,threadName = %s,variablename = %s\n",variableInfoArray[index].lineNumber,variableInfoArray[index].writeOrRead,variableInfoArray[index].threadName,variableInfoArray[index].variableName);
    }
    fclose(pInfo);
    //insertRecordModule();
    return 0;
}

int getLinesOfFile(FILE * pfile)
{
    char text[1024] = "\0";
    int lines = 0;
    while(fgets(text,1024,pfile)!=NULL)//逐行读取fp1所指向文件中的内容到text中
    {
        lines ++;
    }

    return lines;
}

int replaceActions( struct variableInfomation *variableInfo,int lines)
{
    FILE *sourceFile = NULL;
    sourceFile = fopen(TARGET_FILE,"r+");
    if(sourceFile == NULL)
    {
        printf("open file failed\n");
        return -1;
    }

    FILE *tempFile = NULL;
    tempFile = fopen(TEMP_FILE,"w+");
    if(tempFile == NULL)
    {
        printf("open file failed\n");
        return -1;
    }

    int index = 1;
    char text[1024] = "\0";
    int arrayIndex = 0;
    int flag = 0;
    int header = 1;
    while(fgets(text,1024,sourceFile)!=NULL)///逐行读取fp1所指向文件中的内容到text中
    {
        flag = 0;
        //printf("%d-%s\n",index,text);
        ///插入头文件
        if(header)
        {
            if(NULL!= strstr(text,"using namespace std;"))
            {
                FILE *headerFile = fopen(HEADER_FILE,"r");
                char temp[1024];
                if(headerFile == NULL)
                {
                    printf("open file error!\n");
                    return -1;
                }
                while(fgets(temp,1024,headerFile)!=NULL)
                {
                    fputs(temp,tempFile);
                }
                header = 0;
                fclose(headerFile);
            }
        }

        ///变量操作替换为模块入口
        for(arrayIndex = 0;arrayIndex < lines;arrayIndex ++)
        {
            if(index == variableInfo[arrayIndex].lineNumber)
            {
                ///将对变量的读操作替换为函数的入口
                if(0 == variableInfo[arrayIndex].writeOrRead )
                {
                    fprintf(tempFile,"enter_read(\"%s\",\"%s\");\n",variableInfo[arrayIndex].threadName,variableInfo[arrayIndex].variableName);
                    fputs(text,tempFile);
                    flag = 1;
                    break;
                    //printf("enter_read\n");
                }
                ///将对变量的写操作替换为函数入口
                else if(1 == variableInfo[arrayIndex].writeOrRead)
                {
                    fprintf(tempFile,"enter_write(\"%s\",\"%s\");\n",variableInfo[arrayIndex].threadName,variableInfo[arrayIndex].variableName);
                    fputs(text,tempFile);
                    flag = 1;
                    break;
                    //printf("enter_write\n");
                }
                ///在main函数的末尾处对记录的信息输出文件
                else if(2 == variableInfo[arrayIndex].writeOrRead)
                {
                    char temp[1024];
                    FILE *headerToFile = fopen(RECORDTO_FILE,"r");
                    if(headerToFile == NULL)
                    {
                        printf("open file error!\n");
                        return -1;
                    }
                    while(fgets(temp,1024,headerToFile)!=NULL)
                    {
                        fputs(temp,tempFile);
                    }
                    fputs(text,tempFile);
                    flag = 1;
                    fclose(headerToFile);
                    break;
                }
                ///对信号量的初始化
                else if(3 == variableInfo[arrayIndex].writeOrRead)
                {
                    char temp[1024];
                    FILE *semInit = fopen(SEMINIT_FILE,"r");
                    if(semInit == NULL)
                    {
                         printf("open file error!\n");
                        return -1;
                    }
                    while(fgets(temp,1024,semInit)!=NULL)
                    {
                        fputs(temp,tempFile);
                    }
                    fputs(text,tempFile);
                    flag = 1;
                    fclose(semInit);
                    break;
                }
            }
        }
        if(flag == 0)
        {
            fputs(text,tempFile);
        }
        index++;
    }
    fclose(sourceFile);
    fseek( tempFile, 0, SEEK_SET );

    sourceFile = fopen(TARGET_FILE,"w");
    if(sourceFile == NULL)
    {
        printf("open file failed\n");
        return -1;
    }
    ///将临时文件的内容拷贝回原文件
    while(fgets(text,1024,tempFile)!=NULL)
    {
        fputs(text,sourceFile);
    }
    ///在文件末尾插入记录模块
    FILE *recordFile = fopen(RECORD_FILE,"r");
    if(recordFile == NULL)
    {
        printf("open file failed\n");
        return -1;
    }
    while(fgets(text,1024,recordFile)!=NULL)
    {
        fputs(text,sourceFile);
    }
//    while(!feof(recordFile))
//    {
//        fgets(text,1024,recordFile);
//        fputs(text,sourceFile);
//    }

    fclose(recordFile);
    fclose(tempFile);
    fclose(sourceFile);
    return 0;
}
