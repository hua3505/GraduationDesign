    
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

