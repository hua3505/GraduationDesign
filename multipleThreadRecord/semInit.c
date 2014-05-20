    int res = sem_init(&bin_sem, 0, 1);
    if (res != 0)
    {
         printf("Semaphore initialization failed\n");
    }

