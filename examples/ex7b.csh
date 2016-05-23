// Example 2: Move reference via send

var incr: Ref[Num] = ref(0);

fork {
  var n: Num = 0;
  var res: Num = 0;
  // read incr
  var myincr: Num = *(receive(0, Ref[Num]));
  while (3 > n) {
    res = res + receive(1, Num) + myincr;
    n = n + 1;
  }
  send(2, res);
}

send(0, incr);
send(1, 4);
send(1, 24);
send(1, 1);

// write incr:
// *incr = 2;

var result: Ref[Num] = ref(receive(2, Num));
