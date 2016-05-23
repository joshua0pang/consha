var ww: Ref[Num] = ref(0);
fork {
  *ww = 1;
}
*ww = 2;
