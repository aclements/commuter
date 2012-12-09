#pragma once

struct fstest {
  void (*setup)(void);
  int (*call0)(void);
  int (*call1)(void);
  void (*cleanup)(void);
};

extern struct fstest fstests[];

