/*
 * =====================================================================================
 *
 *       Filename:  defuse.c
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
#include <math.h>

typedef struct {
    char shortname[50];
    char fullname[70];
    Ins* instruction; // instruction that added this variable
} Tmps;

typedef struct {
    // contain the short name for gen/kill and long name for rd
    Tmps gen[200];
    int genlen;
    Tmps kill[200];
    int killlen;
    Tmps in[200];
    int inlen;
    Tmps use[20];
    int uselen;
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

static Tmps convertTmp(Blk* blk, Tmp t, Ins* i) {
    Tmps myvar;
    // for gen/kill analysis
    sprintf(myvar.shortname, "%s", t.name);
    // for rd analysis
    sprintf(myvar.fullname, "@%s%%%s", blk->name, t.name);
    myvar.instruction = i;
    return myvar;
}

static bool processBlk(Blk* blk) {
    bool change = false;
    // arrays contain to.val
    Meta* meta = getMeta(blk);
    Tmps chldin[meta->genlen + meta->inlen];
    int chldinlen = 0;
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

    if (blk->s1) {
        Blk* lchild = blk->s1;
        Meta* lmeta = getMeta(lchild);
        // while we have out genvars add them to next block meta
        for (int i=0; i < chldinlen; i++) {
            int index = searchTmpFullName(chldin[i].fullname, lmeta->in, lmeta->inlen);
            if (index < 0) {
                // something new
                lmeta->in[lmeta->inlen++] = chldin[i];
                change = true;
            }
        }
    }

    if (blk->s2) {
        Blk* rchild = blk->s2;
        Meta* rmeta = getMeta(rchild);
        // while we have out genvars add them to next block meta
        for (int i=0; i < chldinlen; i++) {
            int index = searchTmpFullName(chldin[i].fullname, rmeta->in, rmeta->inlen);
            if (index < 0) {
                // something new
                rmeta->in[rmeta->inlen++] = chldin[i];
                change = true;
            }
        }
    }
    return change;
}

static void genKill(Fn* fn) {
  for (Blk *blk = fn->start; blk; blk = blk->link) {
    // arrays contain to.val
    Meta* meta = getMeta(blk);

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
        meta->gen[meta->genlen++] = convertTmp(blk, fn->tmp[i->to.val], i);
        // then we are GEN the variable in this block
    }

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
                Tmps vnew_other = convertTmp(blk_other, fn->tmp[i_other->to.val], i_other);
                if (strcmp(vnew.shortname, vnew_other.shortname) != 0) {
                    // the other assignement instruction is for another variable
                    continue;
                }
                int index = searchTmpFullName(vnew_other.fullname, meta->kill, meta->killlen);
                if (index >= 0) {
                    // already killed THIS var in THIS block
                    continue;
                }
                meta->kill[meta->killlen++] = convertTmp(blk_other, fn->tmp[i_other->to.val], i_other);
                // then we killed that instruction, that assigned to the same variable
            }
        }
    }
  }

}

static void reaching(Fn* fn) {
  bool change = true;
  while (change) {
    change = false;
    for (Blk* blk = fn->start; blk; blk = blk->link) {
        if( processBlk(blk) ) {
            change = true;
        }
    }
  }
}

static void setup(Fn* fn) {
  metamap = (MapItem*) malloc(fn->nblk * sizeof(MapItem));
  metamaplen = fn->nblk;
  metas = (Meta*) malloc(fn->nblk * sizeof(Meta));
  int mm_i = 0;
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    // set len of meta to zero
    metas[mm_i].inlen = 0;
    metas[mm_i].genlen = 0;
    metas[mm_i].killlen = 0;
    metas[mm_i].uselen = 0;
    // connect meta to block
    metamap[mm_i].key = blk;
    metamap[mm_i].value = &metas[mm_i];
    // for every block
    mm_i++;
  }
}

static void readfn (Fn *fn) {
  // setup for analysis
  setup(fn);
  // gen kill analysis
  genKill(fn);
  // reaching definitions analysis
  reaching(fn);

  // need to count uses
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    Meta* meta = getMeta(blk);
    for (Ins* i=blk->ins; i-blk->ins < blk->nins; i++) {
        for (int argc = 0; argc < 2; argc++) {
            // struct Alias { ABot, ALoc ...
            if (Tmp0 <= i->arg[argc].val && i->arg[argc].type <= 1) {
                // if the arg is a variable
                Tmp t = fn->tmp[i->arg[argc].val];
                int index_gen = findTmpWithShortName(t.name, meta->gen, meta->genlen);
                if (index_gen >= 0 && meta->gen[index_gen].instruction < i) {
                    // we gen it in the same block as use it, does not count
                    continue;
                }
                int index_use = findTmpWithShortName(t.name, meta->use, meta->uselen);
                if (index_use >= 0) {
                    // already have this use
                    continue;
                }
                meta->use[meta->uselen++] = convertTmp(blk, fn->tmp[i->arg[argc].val], i);
            }
        }
    }
  }

  for (Blk* blk = fn->start; blk; blk = blk->link) {
    Meta* meta = getMeta(blk);
    printf("@%s", blk->name);
    printf("\n\tdef =");
    for (int i=0; i < meta->genlen; i++) {
        printf(" %%%s", meta->gen[i].shortname);
    }
    printf("\n\tuse =");
    for (int i=0; i < meta->uselen; i++) {
        printf(" %%%s", meta->use[i].shortname);
    }
    printf("\n");
  }
  printf("\n");

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

