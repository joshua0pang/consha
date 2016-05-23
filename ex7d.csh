// Example 4: Share reference via send

var incr: Share[Num] = share(ref(0));

fork {
  var n: Num = 0;
  var res: Num = 0;
  var myincr: Share[Num] = receive(0, Share[Num]);
  while (3 > n) {
    res = res + receive(1, Num) + *(myincr);
    n = n + 1;
  }
  send(2, res);
}

send(0, incr);
send(1, 4);
send(1, 24);
send(1, 1);

// write incr:
*incr = 2;

var result: Ref[Num] = ref(receive(2, Num));
