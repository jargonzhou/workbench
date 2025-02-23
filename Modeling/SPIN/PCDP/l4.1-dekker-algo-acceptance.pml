/*
Algorithm 3.10. Dekker's algorithm

boolean wantp <- false, wantq <- false
integer turn <- 1
-
p:
loop forever
p1: non-critical section
p2: wantp <- true          // 我要
p3: while wantq            // 他要时
p4:   if turn = 2          //   他的机会
p5:     wantp <- false     //     我不要
p6:     await turn = 1     //     等待: 我的机会
p7:     wantp <- true      //     我要
p8: critical section
p9: turn <- 2             // 机会给他
p10: wantp <- false       // 我不要

q:
loop forever
q1: non-critical section
q2: wantq <- true
q3: while wantp
q4:   if turn = 1
q5:     wantq <- false
q6:     await turn = 2
q7:     wantq <- true
q8: critical section
q9: turn <- 1
q10: wantq false
*/

//
// 时序逻辑公式: SPIN Acceptance mode
// []mutex
// []<> nostarve

bool wantp = false, wantq = false;
byte turn = 1;

// 使用辅助变量表达正确性描述
byte critical = 0;

// 互斥
// SPIN中原子命题必须是标识符
#define mutex (critical <= 1)

// 无饥饿
bool PinCS = false;
#define nostarve = PinCS


active proctype p() {
  do :: wantp = true;
    do :: ! wantq -> break;
       :: else ->
            if :: (turn == 1)
               :: (turn == 2) ->
                    wantp = false;
                    (turn == 1);
                    wantp = true
            fi
    od;
    // preprotocol
    critical++;
    PinCS = true;
    PinCS = false;
    critical--;
    // postprotocol
    turn = 2;
    wantp = false
  od
}

active proctype q() {
  do :: wantq = true;
    do :: ! wantp -> break;
       :: else ->
            if :: (turn == 2)
               :: (turn == 1) ->
                    wantq = false;
                    (turn == 2);
                    wantq = true
            fi
    od;
    // preprotocol
    critical++;
    critical--;
    // postprotocol
    turn = 1;
    wantq = false
  od
}