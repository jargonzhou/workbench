// 互斥问题: Dekker互斥算法 1962

bit turn;
bool flag[2];
byte cnt;

active [2] proctype mutext()
{
	pid i,j;
	
	i = _pid;
	j = 1 - _pid;
	
	again:
	flag[i] = true;
	do 
	:: flag[j] -> 
		if 
		:: turn == j -> 
			flag[i] = false;
			(turn != j) -> // wait until true
			flag[i] = true
		:: else -> 
			skip// do nothing
		fi
	:: else -> 
		break// 退出循环
	od;
	
	cnt++;
	assert(cnt == 1);// 关键区域
	cnt--;
	
	turn = j;
	flag[i] = false;
	goto again
}