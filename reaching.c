/*
 * =====================================================================================
 *
 *       Filename:  reaching.cpp
 *
 *    Description:
 *
 *        Version:  1.0
 *        Created:  11/23/2017 06:19:27 PM
 *       Revision:  none
 *       Compiler:  gcc
 *
 *         Author:  Artem Abramov (aa), tematibr@gmail.com
 *   Organization:
 *
 * =====================================================================================
 */

#include <qbe/all.h>
#include <stdio.h>
#include <memory.h>
#include <stdbool.h>
#include <string.h>

typedef struct {
    char shortname[20];
    char fullname[20];
} Tmps;

typedef struct {
    // contain the short name for gen/kill and long name for rd
    Tmps gen[7];
    int genlen;
    Tmps kill[7];
    int killlen;
    Tmps in[7];
    int inlen;
} Meta;

typedef struct {
    Blk* key;
    Meta* value;
} MapItem;

Meta* metas;
MapItem* metamap;
int metamaplen = 0;

Meta* getMeta(Blk *needle) {
    for (int i = 0; i < metamaplen; i++) {
        if (metamap[i].key == needle) {
            return metamap[i].value;
        }
    }
    return NULL;
}

static int findTmpWithShortName(char* short_needle, Tmps* haystack, int hay_len) {
    for (int index = 0; index<hay_len; index++) {
        if (strcmp(haystack[index].shortname, short_needle) == 0) {
            return index;
        }
    }
    return -1;
}

static int searchTmpFullName(char* full_needle, Tmps* haystack, int hay_len) {
    for (int index = 0; index<hay_len; index++) {
        if (strcmp(haystack[index].fullname, full_needle) == 0) {
            return index;
        }
    }
    return -1;
}

static Tmps convertTmp(Blk* blk, Tmp t) {
    Tmps myvar;
    // for gen/kill analysis
    sprintf(myvar.shortname, "%s", t.name);
    // for rd analysis
    sprintf(myvar.fullname, "@%s%%%s", blk->name, t.name);
    return myvar;
}

static bool processBlk(Fn* fn, Blk* blk) {
    bool change = false;
    // arrays contain to.val
    Tmps chldin[200];
    int chldinlen = 0;
    Meta* meta = getMeta(blk);
    for (int i=0; i < meta->inlen; i++) {
        int index = searchTmpFullName(meta->in[i].fullname, meta->kill, meta->killlen);
        if (index < 0) {
            // if not found, then this IN var is transitive, send to next blk
            chldin[chldinlen++] = meta->in[i];
        }
    }

    for (int i=0; i < meta->genlen; i++) {
        chldin[chldinlen++] = meta->gen[i];
    }

    int gen_count = 0;
    Tmps genvars[100];

    for (int i=0; i < meta->inlen; i++) {
        // add meta to our genvars, to unify
        genvars[gen_count++] = meta->in[i];
    }

    for (Ins* i=blk->ins; i-blk->ins < blk->nins; i++) {
        // if we are assigning to a temporary variable and not elsewhere
        if (Tmp0 <= i->to.val) {
            Tmps vnew = convertToChars(blk, fn->tmp[i->to.val]);
            // check if we must override or add new
            int index = findTmpWithName(vnew.name, genvars, gen_count);
            if (index < 0) {
                // we must add new
                genvars[gen_count++] = vnew;
            } else {
                // we must override
                genvars[index] = vnew;
            }
        }
    }

    if (blk->s1) {
        Blk* lchild = blk->s1;
        Meta* lmeta = getMeta(lchild);
        // while we have out genvars add them to next block meta
        for (int i=0; i < gen_count; i++) {
            Tmps vnew = genvars[i];
            int index = findTmpWithName(vnew.name, lmeta->in, lmeta->inlen);
            if (index < 0) {
                // we must add new
                lmeta->in[lmeta->inlen++] = vnew;
                change = true;
            } else {
                // we must override
                lmeta->in[index] = vnew;
            }
        }
    }

    if (blk->s2) {
        Blk* rchild = blk->s2;
        Meta* rmeta = getMeta(rchild);
        // while we have out genvars add them to next block meta
        for (int i=0; i < gen_count; i++) {
            Tmps vnew = genvars[i];
            int index = findTmpWithName(vnew.name, rmeta->in, rmeta->inlen);
            if (index < 0) {
                // we must add new
                rmeta->in[rmeta->inlen++] = vnew;
                change = true;
            } else {
                // we must override
                rmeta->in[index] = vnew;
            }
        }
    }
    return change;
}

static void genKill(Fn* fn) {
  for (Blk *blk = fn->start; blk; blk = blk->link) {
    // arrays contain to.val
    Meta* meta = getMeta(blk);
    printf("@%s", blk->name);
    printf("\n\tgen =");

    for (Ins* i=blk->ins; i-blk->ins < blk->nins; i++) {
        // if we are assigning to a temporary variable and not elsewhere
        if (Tmp0 > i->to.val) {
            continue;
        }
        char* s1 = fn->tmp[i->to.val].name;
        int index = findTmpWithShortName(s1, meta->gen, meta->genlen);
        if (index >= 0) {
            // its not unique
            continue;
        }
        meta->gen[meta->genlen++] = convertTmp(blk, fn->tmp[i->to.val]);
        // then we are GEN the variable in this block
        printf(" @%s%%%s", blk->name, s1);
    }

    printf("\n\tkill =");

    // count down from gen_count
    int k = meta->genlen;
    while (k-- > 0) {
        // search where we might be KILL this variable
        // iterate over all other blocks and instructions
        Tmps vnew = meta->gen[k];
        for (Blk *blk_other = fn->start; blk_other; blk_other = blk_other->link) {
            if (blk_other == blk) {
                // this is the same block as current
                continue;
            }
            for (Ins* i_other=blk_other->ins; i_other-blk_other->ins < blk_other->nins; i_other++) {
                if (Tmp0 > i_other->to.val) {
                    // not a var (assignement)
                    continue;
                }
                Tmps vnew_other = convertTmp(blk_other, fn->tmp[i_other->to.val]);
                if (strcmp(vnew.shortname, vnew_other.shortname) != 0) {
                    // the other assignement instruction is for another variable
                    continue;
                }
                int index = searchTmpFullName(vnew_other.fullname, meta->kill, meta->killlen);
                if (index >= 0) {
                    // already killed THIS var in THIS block
                    continue;
                }
                meta->kill[meta->killlen++] = convertTmp(blk_other, fn->tmp[i_other->to.val]);
                // then we killed that instruction, that assigned to the same variable
                printf(" %s", vnew_other.fullname);
            }
        }
    }
    printf("\n");
  }
  printf("\n");

}

static void readfn (Fn *fn) {
  metamap = (MapItem*) malloc(fn->nblk * sizeof(MapItem));
  metamaplen = fn->nblk;
  metas = (Meta*) malloc(fn->nblk * sizeof(Meta));
  int mm_i = 0;
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    // set len of meta to zero
    metas[mm_i].inlen = 0;
    metas[mm_i].genlen = 0;
    metas[mm_i].killlen = 0;
    // connect meta to block
    metamap[mm_i].key = blk;
    metamap[mm_i].value = &metas[mm_i];
    // for every block
    mm_i++;
  }

  genKill(fn);

  bool change = true;
  while (change) {
    change = false;
    for (Blk* blk = fn->start; blk; blk = blk->link) {
        if( processBlk(fn, blk) ) {
            change = true;
        }
    }
  }

  for (Blk* blk = fn->start; blk; blk = blk->link) {
    printf("@%s", blk->name);
    printf("\n\trd_in =");
    // what have we created and overriden, the final list, this is for the meta of the next block
    Meta* meta = getMeta(blk);
    for (int i=0; i < meta->inlen; i++) {
        printf(" %s", meta->in[i].fullname);
    }
  }

  free(metamap);
  free(metas);
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}

