mtype = {P,C,N};

mtype turn = P;
pid who;

// 内联定义: 类似于C中宏定义执行文本替换
// x等于y时赋值为z, 设置当前进程ID
inline request(x,y,z) {
// atomic with guard condition
atomic {x == y -> x = z;who = _pid}
}

// 将x赋值为y
inline release(x,y) {
atomic {x = y;who = 0}
}

active [2] proctype producer() {
	do 
	:: request(turn,P,N) -> 
		printf("P%d\n",_pid);
		assert(who == _pid);
		release(turn,C)
	od
}

active [2] proctype consumer() {
	do 
	:: request(turn,C,N) -> 
		printf("C%d\n",_pid);
		assert(who == _pid);
		release(turn,P)
	od
}