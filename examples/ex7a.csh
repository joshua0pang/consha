// Example 1: Move reference via scope

var incr: Ref[Num] = ref(0);     // shared, mutable memory

*incr = 1;                       // writes to incr

fork {
  var n: Num = 0;
  var res: Num = 0;
  var myincr: Num = *(incr);     // read incr
  while (3 > n) {
    res = res + receive(1, Num); // add received number to res
    res = res + myincr;          // add myincr
    n = n + 1;
  }
  send(2, res);                  // send final result
}

send(1, 4);
send(1, 24);
send(1, 1);

// *incr = 2;  // writes to incr after forking
               // -> this write would cause a data race and
               //    therefore the type checker rejects this statment

var result: Ref[Num] = ref(receive(2, Num)); // store final result in heap
