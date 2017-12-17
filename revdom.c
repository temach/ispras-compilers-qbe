/*
 * =====================================================================================
 *
 *       Filename:  revdom.c
 *
 *    Description:  Reverse dominators
 *
 *        Version:  1.0
 *        Created:  11/25/2017 02:09:10 PM
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
    // predeccessor (parent) blocks, that point to this block
    Blk* papa[200];
    int papalen;
    // blocks that this block dominates
    Blk* d[200];
    int dlen;
    bool processed;
    // reversed link
    Blk* rlink;
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
    // connect meta to block
    metamap[mm_i].key = blk;
    metamap[mm_i].value = &metas[mm_i];
    // for every block
    mm_i++;
  }
}

static void buildParents(Blk* blk) {
    for (uint i=0; i < blk->npred; i++) {
        Blk* pred = blk->pred[i];
        Meta* pred_meta = getMeta(pred);
        // add yourself to your childs parents array
        pred_meta->papa[pred_meta->papalen++] = blk;
    }
}

static void reverseLink(Fn* fn) {
  // reverse linked list
  Blk* currNode = fn->start;
  Blk* nextNode = NULL;
  Blk* prevNode = NULL;
  while(currNode != NULL) {
      if (! currNode->link) {
          // record the end block
          fn->start = currNode;
      }
      nextNode = currNode->link;
      currNode->link = prevNode;
      prevNode = currNode;
      currNode = nextNode;
  }
}


static void readfn (Fn *fn) {
  // setup for analysis
  setup(fn);

  // reverse the graph, so we start with the new START node
  reverseLink(fn);

  // setup every block to dominate itself
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    Meta* meta = getMeta(blk);
    meta->d[meta->dlen++] = blk;
  }

  // build lists of parents (reverse the graph)
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    buildParents(blk);
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

  // reverse linked list BACK to how it was
  reverseLink(fn);

  for (Blk* blk = fn->start; blk; blk = blk->link) {
    printf("@%s\t", blk->name);
    for (Blk* other_blk = fn->start; other_blk; other_blk = other_blk->link) {
        Meta* other_meta = getMeta(other_blk);
        if (hasBlk(blk, other_meta->d, other_meta->dlen)) {
            // if other_blk has this blk as dominator (in the dom array)
            printf(" @%s", other_blk->name);
        }
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


