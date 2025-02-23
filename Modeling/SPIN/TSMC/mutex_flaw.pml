// 错误的互斥算法

byte cnt;

byte x,y,z;

active [2] proctype user() {
  byte me = _pid + 1; // 1 or 2

again:
  x = me;
  if 
  :: (y == 0 || y == me) -> skip
  :: else -> goto again
  fi;

  z = me;
  if 
  :: (x == me) -> skip
  :: else -> goto again
  fi;

  y = me;
  if 
  :: (z == me) -> skip
  :: else -> goto again
  fi;

  // 进入关键区域
  cnt++;
  assert(cnt == 1);
  cnt--;
  goto again
}