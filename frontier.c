/*
 * =====================================================================================
 *
 *       Filename:  frontier.c
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

typedef struct {
    // pointer to single idom
    Blk* idom;
    // predeccessor (parent) blocks, that point to this block
    Blk* papa[200];
    int papalen;
    // blocks that this block dominates
    Blk* d[200];
    int dlen;
    // processed - used to find dominators
    bool processed;
    // domination frontier for this block
    Blk* front[200];
    int frontlen;
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

static bool hasBlk(Blk* needle, Blk** haystack, int hay_len) {
    for (int index = 0; index<hay_len; index++) {
        if (haystack[index] == needle) {
            return true;
        }
    }
    return false;
}

static bool processBlk(Blk* blk) {
    bool change = false;
    Meta* meta = getMeta(blk);

    for (int i = 0; i < meta->papalen; i++) {
        Blk* parent = meta->papa[i];
        Meta* parentmeta = getMeta(parent);
        for (int index=0; index < parentmeta->dlen; index++) {
            // a candidate for dominating you
            Blk* parent_dom = parentmeta->d[index];
            if (hasBlk(parent_dom, meta->d, meta->dlen)) {
                // you already have this listed as dominating you! (if this is not the first iteration)
                continue;
            }
            // for each block that dominates your parent, check if other parents have it dominating them
            bool all_parents_have_this_blk = true;
            for (int k=0; k < meta->papalen; k++) {
                Blk* other_parent = meta->papa[k];
                if (other_parent == parent) {
                    // when your other_parent is the one you checked first, dont check again
                    continue;
                }
                if (other_parent == blk) {
                    // when your other_parent is yourself
                    // of course you will never have this blk listed as dominator
                    continue;
                }
                Meta* other_parentmeta = getMeta(other_parent);
                if (! other_parentmeta->processed) {
                    // if the other block has not been processed, consider it as no restrictions (anything is ok)
                    continue;
                }
                if (! hasBlk(parent_dom, other_parentmeta->d, other_parentmeta->dlen)) {
                    // one of the parents does NOT have it, (so that block can NOT dominate you)
                    all_parents_have_this_blk = false;
                    break;
                }
            }
            if (all_parents_have_this_blk) {
                // only if all other parents have this block
                // and you have not added it already
                // then add it
                meta->d[meta->dlen++] = parent_dom;
                change = true;
            }
        }
    }

    meta->processed = true;

    return change;
}


static void setup(Fn* fn) {
  metamap = (MapItem*) malloc(fn->nblk * sizeof(MapItem));
  metamaplen = fn->nblk;
  metas = (Meta*) malloc(fn->nblk * sizeof(Meta));
  int mm_i = 0;
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    // set len of meta to zero
    metas[mm_i].papalen = 0;
    metas[mm_i].dlen = 0;
    metas[mm_i].processed = false;
    // set pointers to zero
    metas[mm_i].idom = NULL;
    // connect meta to block
    metamap[mm_i].key = blk;
    metamap[mm_i].value = &metas[mm_i];
    // for every block
    mm_i++;
  }
}

static void buildParents(Fn* fn) {
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    if (blk->s1) {
        Blk* lchild = blk->s1;
        Meta* lmeta = getMeta(lchild);
        // add yourself to your childs parents array
        lmeta->papa[lmeta->papalen++] = blk;
    }

    if (blk->s2) {
        Blk* rchild = blk->s2;
        Meta* rmeta = getMeta(rchild);
        // add yourself to your childs parents array
        rmeta->papa[rmeta->papalen++] = blk;
    }
  }
}

static void findDominators(Fn* fn) {
  // setup every block to dominate itself
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    Meta* meta = getMeta(blk);
    meta->d[meta->dlen++] = blk;
  }

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

static void immediateDominators(Fn* fn) {
  // set idom pointers
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    Meta* meta = getMeta(blk);
    if (meta->dlen < 2) {
        // nobody dominates this blk (only itself)
        continue;
    }
    for (int i=0; i < meta->dlen; i++) {
        Blk* candidate = meta->d[i];
        if (candidate == blk) {
            // you can not be immediate dominator of yourself
            continue;
        }
        bool can_be_idom = true;
        // check that there is no block dominating in between candidate and blk
        for (int k=0; k < meta->dlen; k++) {
            Blk* other_dom = meta->d[k];
            if (other_dom == blk || other_dom == candidate) {
                // skip the blk and skip yourself, because these will of course be true
                continue;
            }
            Meta* other_dom_meta = getMeta(other_dom);
            if (hasBlk(candidate, other_dom_meta->d, other_dom_meta->dlen)) {
                // candidate dominates another block in the chain, its not immediate dominator
                can_be_idom = false;
                break;
            }
        }
        if (can_be_idom) {
            meta->idom = candidate;
            // finish the loop, there is only one idom
            break;
        }
    }
  }
}

static void readfn (Fn *fn) {
  // setup for analysis
  setup(fn);
  // build lists of parents (reverse the graph)
  buildParents(fn);
  // find all the dominators for each node
  findDominators(fn);
  // find all idom
  immediateDominators(fn);

  for (Blk* blk = fn->start; blk; blk = blk->link) {
    Meta* meta = getMeta(blk);
    if (meta->papalen > 0) {
        for (int i=0; i < meta->papalen; i++) {
            Blk* parent = meta->papa[i];
            Blk* r = parent;
            Meta* rmeta = getMeta(r);
            while (r != NULL && r != meta->idom) {
                if (! hasBlk(blk, rmeta->front, rmeta->frontlen)) {
                    rmeta->front[rmeta->frontlen++] = blk;
                }
                r = rmeta->idom;
                rmeta = getMeta(r);
            }
        }
    }
  }


  for (Blk* blk = fn->start; blk; blk = blk->link) {
    printf("@%s:\t", blk->name);
    Meta* meta = getMeta(blk);
    for (int i=0; i < meta->frontlen; i++) {
        printf(" @%s", meta->front[i]->name);
    }
    printf("\n");
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


