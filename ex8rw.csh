var ww: Ref[Num] = ref(0);
fork {
  var n: Num = *(ww);
}
*ww = 2;
