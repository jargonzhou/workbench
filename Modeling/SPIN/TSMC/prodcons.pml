// 生产者-消费者

mtype = {P,C};// 声明符号名称
mtype turn = P;// 全局变量

active proctype producer() 
{
	do// 循环
:: (turn == P) -> // guard语句
	printf("Produce\n");//;作为语句分隔符而不是结束符
	turn = C
od
}

// active proctype producer2()
// {
// again: if// 选择语句
// :: (turn == P) -> 
// printf("Produce\n");
// turn = C
// fi;
// goto again;
// }

// 关键字: else
// wait: if 
// :: (turn == P) -> ...
// :: else -> goto wait
// fi;


active proctype consumer()
{
do 
:: (turn == C) -> 
printf("Consume\n");
turn = P
od
}