#include <stdio.h>
#include "fstest.h"

int
main(int ac, char** av)
{
  for (int i = 0; fstests[i].setup; i++) {
    fstests[i].setup();
    int ra0 = fstests[i].call0();
    int ra1 = fstests[i].call1();
    fstests[i].cleanup();

    fstests[i].setup();
    int rb1 = fstests[i].call1();
    int rb0 = fstests[i].call0();
    fstests[i].cleanup();

    if (ra0 == rb0 && ra1 == rb1) {
      printf("test %d: commutes\n", i);
    } else {
      printf("test %d: diverges: %d %d vs %d %d\n", i, ra0, ra1, rb0, rb1);
    }
  }
}
