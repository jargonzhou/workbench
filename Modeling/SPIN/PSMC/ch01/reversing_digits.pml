active proctype P() {
	int value = 123;/* Try with a byte variable here ...*/ 
	int reversed;/* ... and here!*/ 
	reversed = 
	(value % 10) * 100 + 
	((value / 10) % 10) * 10 + 
	(value / 100);
	printf("value = %d,reversed = %d\n",value,reversed)
}
