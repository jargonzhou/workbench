chan request = [0] of { byte, chan };

active [2] proctype Server() {
  byte client;
  chan replyChannel;
end:
  do
  :: request ? client, replyChannel ->
    printf("Client %d processed by server %d\n",
      client, _pid);
    replyChannel ! _pid, client
  od
}

active [2] proctype Client() {
  byte server;
  byte whichClient;
  chan reply = [0] of { byte, byte };
  request ! _pid, reply;
  reply ? server, whichClient;
  printf("Reply received from server %d by client %d\n",
    server, _pid);
  assert(whichClient == _pid)
}