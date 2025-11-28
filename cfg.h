/**
 * Author:    Grigory Fedyukovich, Subhadeep Bhattacharya
 * Created:   09/30/2020
 *
 * (c) FSU
 **/

#include <stdbool.h>
#include <stdlib.h>

struct cfg {int src; int dst; bool valid; bool final; struct cfg* next; char* fun; };

void push_cfg (int src, int dst, bool valid, bool final, struct cfg** r, struct cfg** t);

void push_ncfg (int src, int dst, bool valid, bool final, char* fun, struct cfg** r, struct cfg** t);

int get_max_id (struct cfg* r);
