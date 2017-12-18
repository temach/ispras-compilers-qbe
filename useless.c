/*
 * =====================================================================================
 *
 *       Filename:  useless.c
 *
 *    Description:  Dead code elimination.
 *
 *        Version:  1.0
 *       Revision:  none
 *       Compiler:  gcc
 *
 *         Author:  Artem Abramov (aa), tematibr@gmail.com
 *
 * =====================================================================================
 */


#include <qbe/all.h>
#include <stdio.h>
#include <memory.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>

Ins* worklist[200];
int worklist_len = 0;

typedef struct {
    bool critical;
    Blk* block;
} Meta;

typedef struct {
    Ins* key;
    Meta* value;
} MapItem;

Meta* metas;
MapItem* metamap;
int metamaplen = 0;

Meta* getMeta(Ins *needle) {
    for (int i = 0; i < metamaplen; i++) {
        if (metamap[i].key == needle) {
            return metamap[i].value;
        }
    }
    return NULL;
}

static bool hasItem(Ins* needle, Ins** haystack, int hay_len) {
    for (int index = 0; index<hay_len; index++) {
        if (haystack[index] == needle) {
            return true;
        }
    }
    return false;
}

static Ins* definitionIns(Fn* fn, char* ssa_needle) {
    for (int index = 0; index < metamaplen; index++) {
        // get id of the target variable from the operation
        uint tmp_id = metamap[index].key->to.val;
        if (strcmp(fn->tmp[tmp_id].name, ssa_needle) == 0) {
            // if the name of the target variable equals ssa_needle, then this is the instruction
            // that defined the variable with such an ssa_needle
            return metamap[index].key;
        }
    }
    return NULL;
}



static void setup(Fn* fn) {
  metamap = (MapItem*) malloc(200 * sizeof(MapItem));
  metamaplen = 200;
  metas = (Meta*) malloc(200 * sizeof(Meta));
  int mm_i = 0;
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
        // set len of meta to zero
        // metas[mm_i].critical = false;
        // connect meta to block
        metamap[mm_i].key = i;
        metamap[mm_i].value = &metas[mm_i];
        // for every instruction
        mm_i++;
    }
  }
  metamaplen = mm_i;
}


static void mark(Fn* fn) {
    // also mark ret and call as critical

    // mark store as critical
    for (Blk* blk = fn->start; blk; blk = blk->link) {
        for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
            Meta* meta = getMeta(i);
            meta->critical = false;
            if (Ostoreb < i->op && i->op < Ostored) {
                // if this instruction writes to memory
                meta->critical = true;
                // analyse this instruction later
                worklist[worklist_len++] = i;
            }
        }
    }

    while (worklist_len > 0) {
        Ins* i = worklist[worklist_len--];
        if (i->arg[0].val >= Tmp0) {
            // if we used a variable as argument in critical operation
            char* name_of_used_val = fn->tmp[i->arg[0].val].name;
            Ins* variable_def = definitionIns(fn, name_of_used_val);
            Meta* var_def_meta = getMeta(variable_def);
            if (var_def_meta->critical == true) {
                // we have already marked it as critical
                continue;
            }
            // that instruction that defined the variable we use now, well its also critical
            var_def_meta->critical = true;
            worklist[worklist_len++] = variable_def;
        }
        if (i->arg[1].val >= Tmp0) {
            // NOW THE SAME FOR ARG 2
            // if we used a variable as argument in critical operation
            char* name_of_used_val = fn->tmp[i->arg[1].val].name;
            Ins* variable_def = definitionIns(fn, name_of_used_val);
            Meta* var_def_meta = getMeta(variable_def);
            if (var_def_meta->critical == true) {
                // we have already marked it as critical
                continue;
            }
            // that instruction that defined the variable we use now, well its also critical
            // NOW THE SAME FOR ARG 2
            var_def_meta->critical = true;
            worklist[worklist_len++] = variable_def;
        }
        // now process reverse frontier graph
        Meta* meta = getMeta(i);
    }


}

static void sweep(Fn* fn) {

}

static int useful(Ins* i) {
    return false;
}


static void readfn (Fn *fn) {
    fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
    fillpreds(fn);
    filluse(fn);
    ssa(fn);

    setup(fn);

    for (Blk *blk = fn->start; blk; blk = blk->link) {
        for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
            if (! useful(i)) {
                i->op = Onop;
                i->to = R;
                i->arg[0] = R;
                i->arg[1] = R;
            }
        }
    }

    fillpreds(fn); // Either call this, or keep track of preds manually when rewriting branches.
    fillrpo(fn); // As a side effect, fillrpo removes any unreachable blocks.
    printfn(fn, stdout);
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
