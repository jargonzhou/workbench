// 数据传输协议

mtype = {ini,ack,dreq,data,shutup,quiet,dead};

// 通道
chan M = [1] of {mtype};
chan W = [1] of {mtype};

active proctype Mproc()
{
	W!ini;// 连接
	M?ack;// 握手
	
	timeout -> // wait
	if// 两个选项
:: W!shutup// 开始关闭
:: W!dreq;// 或: 请求数据接收数据
	M?data -> 
	do 
	:: W!data// 发送数据
	:: W!shutup;// 或: 关闭
		break
	od
fi;

M?shutup;// 关闭的握手
W!quiet;
M?dead
}

active proctype Wproc()
{
W?ini;// 等待ini
M!ack;// 确认

do// 三个选项
:: W?dreq -> // 请求数据时
M!data// 发送数据
:: W?data -> // 接收数据时
skip// 无响应
:: W?shutup -> 
M!shutup;// 开始关闭
break
od;

W?quiet;
M!dead
}