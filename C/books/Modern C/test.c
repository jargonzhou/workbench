    #include <stdlib.h>
    
    char *p;  
   
    __asm__("pushf\n"  
            "orl $0x40000, (%rsp)\n"  
            "popf");  
   
    /*  
     * malloc() always provides aligned memory. 
     * Do not use stack variable like a[9], depending on the compiler you use, 
     * a may not be aligned properly. 
     */  
    p = malloc(sizeof(int) + 1);  
    memset(p, 0, sizeof(int) + 1);  
  
    /* making p unaligned */  
    p++;  
  
    printf("%d\n", *(int *)p);  