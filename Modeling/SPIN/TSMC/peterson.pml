// 互斥问题: Peterson算法 1981

bool turn,flag[2];
byte cnt;

active [2] proctype P1()
{
	pid i,j;
	
	i = _pid;
	j = 1 - _pid;
	
	again:
	flag[i] = true;
	turn = i;
	(flag[j] == false || turn != i) -> // wait until true
	
	cnt++;
	assert(cnt == 1);
	cnt--;
	
	flag[i] = false;
	goto again
}