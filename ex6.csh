var c0: Num = 0;
var c1: Num = 1;

send(c0, 12);
send(c1, true);

var n: Ref[Num] = ref(0);
var r1: Bool = receive(c1, Bool);
if (r1) {
  *n = receive(c0, Num);
}
