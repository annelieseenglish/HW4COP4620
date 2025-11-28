/**
 * Author:    Grigory Fedyukovich, Subhadeep Bhattacharya
 * Created:   09/30/2020
 *
 * (c) FSU
 **/

#include "cfg.h"

void push_ncfg (int src, int dst, bool valid, bool final, char* fun, struct cfg** r, struct cfg** t)
{
  if (*r == NULL){
    *r = (struct cfg*)malloc(sizeof(struct cfg));
    (*r)->src = src;
    (*r)->dst = dst;
    (*r)->valid = valid;
    (*r)->final = final;
    (*r)->next = NULL;
    (*r)->fun = fun;
    *t = *r;
  }
  else{
    struct cfg* ptr;
    ptr = (struct cfg*)malloc(sizeof(struct cfg));
    ptr->src = src;
    ptr->dst = dst;
    ptr->valid = valid;
    ptr->final = final;
    ptr->next = NULL;
    ptr->fun = fun;
    (*t)->next = ptr;
    (*t) = ptr;
  }
}

void push_cfg (int src, int dst, bool valid, bool final, struct cfg** r, struct cfg** t)
{
  push_ncfg(src, dst, valid, final, (*t)->fun, r, t);
}

int get_max_id (struct cfg* r){
  struct cfg* t = r;
  int tmp = 0;
  while (t != NULL){
    if (t->valid && tmp < t->dst) tmp = t->dst;
    t = t->next;
  }
  return tmp;
}
