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

    // jmp marks
    bool jmp_is_critical;

    // phi marks
    Phi* crit_phi[50];
    int crit_phi_len;

    // ins marks
    Ins* crit_ins[50];
    int crit_ins_len;
} BlkMeta;

typedef struct {
    Blk* key;
    BlkMeta* value;
} BlkMapItem;

BlkMeta* bmetas;
BlkMapItem* bmetamap;
int bmetamaplen = 0;

BlkMeta* getBlkMeta(Blk *needle) {
    for (int i = 0; i < bmetamaplen; i++) {
        if (bmetamap[i].key == needle) {
            return bmetamap[i].value;
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
    BlkMeta* meta = getBlkMeta(blk);

    for (int i = 0; i < meta->papalen; i++) {
        Blk* parent = meta->papa[i];
        BlkMeta* parentmeta = getBlkMeta(parent);
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
                BlkMeta* other_parentmeta = getBlkMeta(other_parent);
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


static void setupBlk(Fn* fn) {
  bmetamap = (BlkMapItem*) malloc(fn->nblk * sizeof(BlkMapItem));
  bmetamaplen = fn->nblk;
  bmetas = (BlkMeta*) malloc(fn->nblk * sizeof(BlkMeta));
  int mm_i = 0;
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    // set default values for meta
    bmetas[mm_i].papalen = 0;
    bmetas[mm_i].dlen = 0;
    bmetas[mm_i].frontlen = 0;
    bmetas[mm_i].processed = false;
    bmetas[mm_i].idom = NULL;
    bmetas[mm_i].jmp_is_critical = false;
    bmetas[mm_i].crit_ins_len = 0;
    bmetas[mm_i].crit_phi_len = 0;
    // connect meta to block
    bmetamap[mm_i].key = blk;
    bmetamap[mm_i].value = &bmetas[mm_i];
    // for every block
    mm_i++;
  }
}

static void buildParents(Fn* fn) {
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    for (uint i=0; i < blk->npred; i++) {
        Blk* pred = blk->pred[i];
        BlkMeta* pred_meta = getBlkMeta(pred);
        // add yourself to your childs parents array
        pred_meta->papa[pred_meta->papalen++] = blk;
    }
  }
}

static void findDominators(Fn* fn) {
  // setupBlk every block to dominate itself
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    BlkMeta* meta = getBlkMeta(blk);
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
    BlkMeta* meta = getBlkMeta(blk);
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
            BlkMeta* other_dom_meta = getBlkMeta(other_dom);
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

static void blockAnalyse(Fn* fn) {
  // setup for analysis
  setupBlk(fn);

  // reverse the graph, so we start with the new START node
  reverseLink(fn);

  // build lists of parents (reverse the graph)
  buildParents(fn);
  // find all the dominators for each node
  findDominators(fn);
  // find all idom
  immediateDominators(fn);

  for (Blk* blk = fn->start; blk; blk = blk->link) {
    BlkMeta* meta = getBlkMeta(blk);
    if (meta->papalen > 0) {
        for (int i=0; i < meta->papalen; i++) {
            Blk* parent = meta->papa[i];
            Blk* r = parent;
            BlkMeta* rmeta = getBlkMeta(r);
            while (r != NULL && r != meta->idom) {
                if (! hasBlk(blk, rmeta->front, rmeta->frontlen)) {
                    rmeta->front[rmeta->frontlen++] = blk;
                }
                r = rmeta->idom;
                rmeta = getBlkMeta(r);
            }
        }
    }
  }

  // reverse the graph so its the same again
  reverseLink(fn);
}

enum OPTYPE {
    JUMP,
    PHI,
    INS,
    NONE,
};

// create instance of this struct before adding a
// new item to worklist, this is an intermediate representation
typedef struct {
    enum OPTYPE type;
    Blk* block;
    // if not jump
    Ins* ins_info;
    // if its a jump
    Blk* jmp_info;
    // if its a phi
    Phi* phi_info;
} WorkItem;

WorkItem worklist[200];
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

static WorkItem definitionIns(Fn* fn, char* ssa_needle) {
    // search through all ins and phi in program
    for (Blk* b=fn->start; b; b = b->link) {
        for (Ins *i = b->ins; i < &b->ins[b->nins]; ++i) {
            uint tmp_id = i->to.val;
            if (strcmp(fn->tmp[tmp_id].name, ssa_needle) == 0) {
                // if the name of the target variable equals ssa_needle, then this is the instruction
                // that defined the variable with such an ssa_needle
                WorkItem wi = { .block = b, .type = INS, .ins_info = i};
                return wi;
            }
        }
        for (Phi* p=b->phi; p; p = p->link){
            uint tmp_id = p->to.val;
            if (strcmp(fn->tmp[tmp_id].name, ssa_needle) == 0) {
                WorkItem wi = { .block = b, .type = PHI, .phi_info = p};
                return wi;
            }
        }
    }
    WorkItem wi = { .block = NULL, .type = NONE };
    return wi;
}





static void mark(Fn* fn) {
    // mark store, call and ret as critical
    for (Blk* blk = fn->start; blk; blk = blk->link) {
        BlkMeta* meta = getBlkMeta(blk);
        // all instructions are useless
        meta->crit_ins_len = 0;
        for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
            if ( (Ostoreb <= i->op && i->op <= Ostored)
                    || (i->op == Ocall || i->op == Ovacall)
                )
            {
                // if this instruction writes to memory or call a function
                // analyse this instruction later
                WorkItem wi = { .block = blk, .type = INS, .ins_info = i };
                worklist[worklist_len++] = wi;
            }
        }
        // block has only one jump, check if its a return
        // we store meta info for the jump in the block meta info
        BlkMeta* jmp_meta = getBlkMeta(blk);
        jmp_meta->jmp_is_critical = false;
        if (Jret0 <= blk->jmp.type && blk->jmp.type <= Jretc) {
            // this jump is critical
            // set up to analyse this jump later
            WorkItem wi = { .block = blk, .type = JUMP, .jmp_info = blk };
            worklist[worklist_len++] = wi;
        }
    }

    while (worklist_len > 0) {
        WorkItem i = worklist[--worklist_len];
        if (i.type == INS) {
            BlkMeta* meta = getBlkMeta(i.block);
            if (hasItem(i.ins_info, meta->crit_ins, meta->crit_ins_len)) {
                // already marked this
                continue;
            }
            meta->crit_ins[meta->crit_ins_len++] = i.ins_info;
            // decide to loop once or twice, depends if instruction is one arg or two arg
            int argc = (i.ins_info->arg[1].type > 0 || i.ins_info->arg[1].val >= Tmp0) ? 1 : 2;
            for (int index=0; index < argc; index++) {
                if (i.ins_info->arg[index].val < Tmp0) {
                    // if the critical operation uses a constant
                    continue;
                }
                // if the critical operation uses a variable
                char* name_of_used_val = fn->tmp[i.ins_info->arg[index].val].name;
                // find where that variable is defined
                WorkItem variable_def = definitionIns(fn, name_of_used_val);
                // that instruction that defined the variable we use now, well its also critical
                worklist[worklist_len++] = variable_def;
            }
        } else if (i.type == JUMP) {
            BlkMeta* jmp_meta = getBlkMeta(i.jmp_info);
            if (jmp_meta->jmp_is_critical) {
                // already marked this
                continue;
            }
            jmp_meta->jmp_is_critical = true;
            if (i.jmp_info->jmp.type > 0
                    && (i.ins_info->arg[1].type > 0 || i.ins_info->arg[1].val >= Tmp0)
               )
            {
                // if the critical jump uses some variable
                char* name_of_used_val = fn->tmp[i.jmp_info->jmp.arg.val].name;
                // find where that variable is defined
                WorkItem variable_def = definitionIns(fn, name_of_used_val);
                // that instruction that defined the variable we use now, well its also critical
                worklist[worklist_len++] = variable_def;
            }
        } else if (i.type == PHI) {
            BlkMeta* blk 
        }
        // now process reverse frontier graph
        Blk* enclosing_block = i.block;
        BlkMeta* bmeta = getBlkMeta(enclosing_block);
        for (int i=0; i < bmeta->frontlen; i++) {
            // find instruction that ends frontier blk
            Blk* frontier_blk = bmeta->front[i];
            printf(" @%s", frontier_blk->name);
            BlkMeta* frontier_meta = getBlkMeta(frontier_blk);
            if (frontier_meta->jmp_is_critical) {
                // we have already marked as critical
                continue;
            }
            // and mark that instruction as critical
            frontier_meta->jmp_is_critical = true;
            WorkItem wi = { .block = frontier_blk, .type = JUMP, .jmp_info = frontier_blk };
            worklist[worklist_len++] = wi;
        }
    }
}

static void sweep(Fn* fn) {
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        BlkMeta* meta = getBlkMeta(blk);
        for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
            if (! hasItem(i, meta->crit_ins, meta->crit_ins_len)) {
                i->op = Onop;
                i->to = R;
                i->arg[0] = R;
                i->arg[1] = R;
            }
        }
    }
}


static void readfn (Fn *fn) {
    fillrpo(fn); // Traverses the CFG in reverse post-order, filling blk->id.
    fillpreds(fn);
    filluse(fn);
    ssa(fn);

    blockAnalyse(fn);

    mark(fn);
    sweep(fn);

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
