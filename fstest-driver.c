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
      printf("test %d: commutes: %s->%d %s->%d\n",
             i, fstests[i].call0name, ra0, fstests[i].call1name, ra1);
    } else {
      printf("test %d: diverges: %s->%d %s->%d vs %s->%d %s->%d\n",
             i, fstests[i].call0name, ra0, fstests[i].call1name, ra1,
                fstests[i].call0name, rb0, fstests[i].call1name, rb1);
    }
  }
}
