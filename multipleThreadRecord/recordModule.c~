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
