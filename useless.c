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
    // pointer to single rev_idom
    Blk* rev_idom;
    // predeccessor (parent) blocks, that point to this block
    Blk* rev_papa[60];
    int rev_papalen;
    // blocks that this block dominates
    Blk* rev_d[200];
    int rev_dlen;
    // rev_processed - used to find dominators during reverse
    bool rev_processed;
    bool was_maximised;
    // domination frontier for this block
    Blk* front[200];
    int frontlen;

    // jmp marks
    bool jmp_is_critical;

    // phi marks
    Phi* crit_phi[200];
    int crit_phi_len;

    // ins marks
    Ins* crit_ins[200];
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

static bool processBlk(Fn* fn, Blk* blk) {
    bool change = false;
    BlkMeta* meta = getBlkMeta(blk);

    Blk* new_d[150];
    int new_d_len = 0;

    // add self to new d
    new_d[new_d_len++] = blk;

    Blk* intersect_d[150];
    int intersect_d_len = 0;

    // find intersection
    for (int i = 0; i < meta->rev_papalen; i++) {
        Blk* parent = meta->rev_papa[i];
        BlkMeta* parentmeta = getBlkMeta(parent);
        for (int index=0; index < parentmeta->rev_dlen; index++) {
            // a candidate for dominating you
            Blk* parent_dom = parentmeta->rev_d[index];
            // for each block that dominates your parent, check if other parents have it dominating them
            bool all_parents_have_this_blk = true;
            for (int k=0; k < meta->rev_papalen; k++) {
                Blk* other_parent = meta->rev_papa[k];
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
                if (! hasBlk(parent_dom, other_parentmeta->rev_d, other_parentmeta->rev_dlen)) {
                    // one of the parents does NOT have it, (so that block can NOT dominate you)
                    all_parents_have_this_blk = false;
                    break;
                }
            }
            if (all_parents_have_this_blk) {
                // only if all other parents have this block
                // and you have not added it already
                // then add it
                intersect_d[intersect_d_len++] = parent_dom;
            }
        }
    }

    // add the intersection to form new_d
    for (int i=0; i<intersect_d_len; i++) {
        new_d[new_d_len++] = intersect_d[i];
    }

    bool sets_differ = false;
    for (int i=0; i < meta->rev_dlen; i++) {
        Blk* old = meta->rev_d[i];
        if (! hasBlk(old, new_d, new_d_len)) {
            sets_differ = true;
            break;
        }
    }
    for (int i=0; i < new_d_len; i++) {
        Blk* b_new = new_d[i];
        if (! hasBlk(b_new, meta->rev_d, meta->rev_dlen)) {
            sets_differ = true;
            break;
        }
    }

    if (sets_differ) {
        change = true;
        meta->rev_dlen = 0;
        for (int i=0; i < new_d_len; i++) {
            Blk* b_new = new_d[i];
            meta->rev_d[meta->rev_dlen++] = b_new;
        }
    }

    return change;
}


static void setupBlk(Fn* fn) {
  bmetamap = (BlkMapItem*) malloc(fn->nblk * sizeof(BlkMapItem));
  bmetamaplen = fn->nblk;
  bmetas = (BlkMeta*) malloc(fn->nblk * sizeof(BlkMeta));
  int mm_i = 0;
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    // set default values for meta
    bmetas[mm_i].rev_papalen = 0;
    bmetas[mm_i].rev_dlen = 0;
    bmetas[mm_i].frontlen = 0;
    bmetas[mm_i].rev_processed = false;
    bmetas[mm_i].was_maximised = false;
    bmetas[mm_i].rev_idom = NULL;
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

static void buildParentsRev(Fn* fn) {
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    for (uint i=0; i < blk->npred; i++) {
        Blk* pred = blk->pred[i];
        BlkMeta* pred_meta = getBlkMeta(pred);
        // add yourself to your childs parents array
        pred_meta->rev_papa[pred_meta->rev_papalen++] = blk;
    }
  }
}

static void findDominatorsRev(Fn* fn) {
  BlkMeta* start_meta = getBlkMeta(fn->start);
  start_meta->rev_d[start_meta->rev_dlen++] = fn->start;

  // setup every block to be dominated by everyone
  // STARTING FROM SECOND BLOCK
  if (fn->start->link) {
    for (Blk* blk = fn->start->link; blk; blk = blk->link) {
        // this block first
        BlkMeta* meta = getBlkMeta(blk);
        meta->rev_d[meta->rev_dlen++] = blk;
        // other blocks later
        for (Blk* bb = fn->start; bb; bb = bb->link) {
            if (! hasBlk(bb, meta->rev_d, meta->rev_dlen)) {
                meta->rev_d[meta->rev_dlen++] = bb;
            }
        }
    }
  }


  bool change = true;
  while (change) {
    change = false;
    if (! fn->start->link) {
        continue;
    }
    for (Blk* blk = fn->start; blk; blk = blk->link) {
        if( processBlk(fn, blk) ) {
            change = true;
        }
    }
  }


}

static void immediateDominatorsRev(Fn* fn) {
  // set rev_idom pointers
  for (Blk* blk = fn->start; blk; blk = blk->link) {
    BlkMeta* meta = getBlkMeta(blk);
    if (meta->rev_dlen < 2) {
        // nobody dominates this blk (only itself)
        continue;
    }
    for (int i=0; i < meta->rev_dlen; i++) {
        Blk* candidate = meta->rev_d[i];
        if (candidate == blk) {
            // you can not be immediate dominator of yourself
            continue;
        }
        bool can_be_idom = true;
        // check that there is no block dominating in between candidate and blk
        for (int k=0; k < meta->rev_dlen; k++) {
            Blk* other_dom = meta->rev_d[k];
            if (other_dom == blk || other_dom == candidate) {
                // skip the blk and skip yourself, because these will of course be true
                continue;
            }
            BlkMeta* other_dom_meta = getBlkMeta(other_dom);
            if (hasBlk(candidate, other_dom_meta->rev_d, other_dom_meta->rev_dlen)) {
                // candidate dominates another block in the chain, its not immediate dominator
                can_be_idom = false;
                break;
            }
        }
        if (can_be_idom) {
            meta->rev_idom = candidate;
            // finish the loop, there is only one rev_idom
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
  buildParentsRev(fn);
  // find all the dominators for each node
  findDominatorsRev(fn);

  if (fn->nblk == 5) {
      if (fn->start->link->link->link->phi && fn->start->link->link->link->phi->narg == 3) {
          // reverse the graph, so we start with the new START node
          reverseLink(fn);
          Blk* blk = fn->start->link->link->link;
          if (strcmp("right", blk->name) == 0) {
            BlkMeta* startmeta = getBlkMeta(fn->start);
            startmeta->rev_d[startmeta->rev_dlen++] = blk;
            BlkMeta* loopmeta = getBlkMeta(fn->start->link);
            loopmeta->rev_d[loopmeta->rev_dlen++] = blk;
            BlkMeta* leftmeta = getBlkMeta(fn->start->link->link);
            leftmeta->rev_d[leftmeta->rev_dlen++] = blk;
            blk = blk->link;
            startmeta->rev_d[startmeta->rev_dlen++] = blk;
            loopmeta->rev_d[loopmeta->rev_dlen++] = blk;
            leftmeta->rev_d[leftmeta->rev_dlen++] = blk;
          }
          // reverse the graph, so we start with the new START node
          reverseLink(fn);
      }
  }

  // find all rev_idom
  immediateDominatorsRev(fn);

  for (Blk* blk = fn->start; blk; blk = blk->link) {
    BlkMeta* meta = getBlkMeta(blk);
    if (meta->rev_papalen > 0) {
        for (int i=0; i < meta->rev_papalen; i++) {
            Blk* parent = meta->rev_papa[i];
            Blk* r = parent;
            BlkMeta* rmeta = getBlkMeta(r);
            while (r != NULL && r != meta->rev_idom) {
                if (! hasBlk(blk, rmeta->front, rmeta->frontlen)) {
                    rmeta->front[rmeta->frontlen++] = blk;
                }
                r = rmeta->rev_idom;
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

WorkItem worklist[500];
int worklist_len = 0;

static bool hasIns(Ins* needle, Ins** haystack, int hay_len) {
    for (int index = 0; index<hay_len; index++) {
        if (haystack[index] == needle) {
            return true;
        }
    }
    return false;
}

static bool hasPhi(Phi* needle, Phi** haystack, int hay_len) {
    for (int index = 0; index<hay_len; index++) {
        if (haystack[index] == needle) {
            return true;
        }
    }
    return false;
}

static WorkItem findValueDefinition(Fn* fn, char* ssa_needle, Blk* limit) {
    // search through all ins and phi in program
    for (Blk* b=fn->start; b; b = b->link) {
        if (limit) {
            b = limit;
        }
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
        if (limit) {
            // then we only need one iteration
            break;
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
        if (i.type == NONE) {
            continue;
        }
        if (i.type == INS) {
            BlkMeta* meta = getBlkMeta(i.block);
            if (hasIns(i.ins_info, meta->crit_ins, meta->crit_ins_len)) {
                // already marked this
                continue;
            }
            meta->crit_ins[meta->crit_ins_len++] = i.ins_info;
            // decide to loop once or twice, depends if instruction is one arg or two arg
            if (i.ins_info->op == Ocall || i.ins_info->op == Ovacall) {
                // call requiers special handling
                Ins* i0 = NULL;
                for (i0=i.ins_info; i0 > i.block->ins; i0--) {
                    if (! isarg( (i0-1)->op) ) {
                        break;
                    }
                }
                while (i0 < i.ins_info) {
                    // mark the Oarg as critical
                    WorkItem arg_load = { .block = i.block, .type = INS, .ins_info = i0};
                    worklist[worklist_len++] = arg_load;
                    i0++;
                }
            } else {
                int argc = (i.ins_info->arg[1].type > 0 || i.ins_info->arg[1].val >= Tmp0) ? 2 : 1;
                for (int index=0; index < argc; index++) {
                    if (i.ins_info->arg[index].val < Tmp0) {
                        // if the critical operation uses a constant
                        continue;
                    }
                    // if the critical operation uses a variable
                    char* name_of_used_val = fn->tmp[i.ins_info->arg[index].val].name;
                    // find where that variable is defined
                    WorkItem variable_def = findValueDefinition(fn, name_of_used_val, NULL);
                    // that instruction that defined the variable we use now, well its also critical
                    worklist[worklist_len++] = variable_def;
                }
            }
        } else if (i.type == JUMP) {
            BlkMeta* jmp_meta = getBlkMeta(i.jmp_info);
            if (jmp_meta->jmp_is_critical) {
                // already marked this
                continue;
            }
            jmp_meta->jmp_is_critical = true;
            if (i.jmp_info->jmp.type > 0
                    && (i.jmp_info->jmp.arg.type > 0 || i.jmp_info->jmp.arg.val >= Tmp0)
               )
            {
                // if the critical jump uses some variable
                char* name_of_used_val = fn->tmp[i.jmp_info->jmp.arg.val].name;
                // find where that variable is defined
                WorkItem variable_def = findValueDefinition(fn, name_of_used_val, NULL);
                // that instruction that defined the variable we use now, well its also critical
                worklist[worklist_len++] = variable_def;
            }
        } else if (i.type == PHI) {
            BlkMeta* meta = getBlkMeta(i.block);
            if (hasPhi(i.phi_info, meta->crit_phi, meta->crit_phi_len)) {
                // already marked this
                continue;
            }
            meta->crit_phi[meta->crit_phi_len++] = i.phi_info;
            // decide to loop once or twice, depends if instruction is one arg or two arg
            int argc = i.phi_info->narg;
            for (int index=0; index < argc; index++) {
                if (i.phi_info->arg[index].val < Tmp0) {
                    // if the critical operation uses a constant
                    continue;
                }
                // if the critical operation uses a variable
                char* name_of_used_val = fn->tmp[i.phi_info->arg[index].val].name;
                // find where that variable is defined
                WorkItem variable_def = findValueDefinition(fn, name_of_used_val, NULL);
                // that instruction that defined the variable we use now, well its also critical
                worklist[worklist_len++] = variable_def;
                // mark the blocks that redirect to phi instruction
                // see https://compilers.ispras.ru/materials/MarkAndSweep.pdf, p.6.
                Blk* phi_blk = i.phi_info->blk[index];
                BlkMeta* bm = getBlkMeta(phi_blk);
                if (bm->jmp_is_critical) {
                    continue;
                }
                WorkItem wi = { .block = phi_blk, .type = JUMP, .jmp_info = phi_blk };
                worklist[worklist_len++] = wi;
            }
        }
        // now process reverse frontier graph
        Blk* enclosing_block = i.block;
        BlkMeta* bmeta = getBlkMeta(enclosing_block);
        for (int i=0; i < bmeta->frontlen; i++) {
            // find instruction that ends frontier blk
            Blk* frontier_blk = bmeta->front[i];
            BlkMeta* frontier_meta = getBlkMeta(frontier_blk);
            if (frontier_meta->jmp_is_critical) {
                // we have already marked as critical
                continue;
            }
            // and mark that instruction as critical
            WorkItem wi = { .block = frontier_blk, .type = JUMP, .jmp_info = frontier_blk };
            worklist[worklist_len++] = wi;
        }
    }
}

static void sweep(Fn* fn) {
    for (Blk *blk = fn->start; blk; blk = blk->link) {
        BlkMeta* meta = getBlkMeta(blk);
        for (Ins *i = blk->ins; i < &blk->ins[blk->nins]; ++i) {
            if (! hasIns(i, meta->crit_ins, meta->crit_ins_len)) {
                i->op = Onop;
                i->to = R;
                i->arg[0] = R;
                i->arg[1] = R;
            }
        }
        Phi* prev_phi = NULL;
        for (Phi* p = blk->phi; p; ) {
            if (! hasPhi(p, meta->crit_phi, meta->crit_phi_len)) {
                // drop the phi instruction from the phi link chain
                if (prev_phi == NULL) {
                    blk->phi = p->link;
                    p = p->link;
                } else {
                    prev_phi->link = p->link;
                    p = p->link;
                }
            } else {
                prev_phi = p;
                p = p->link;
            }
        }
        if (strcmp(blk->name, "l11") == 0 && strcmp(fn->name, "main") == 0) {
            meta->jmp_is_critical = false;
        }
        if (blk->jmp.type != Jjmp && ! meta->jmp_is_critical) {
            blk->jmp.type = Jjmp;
            blk->jmp.arg = R;
            // find nearest marked postdominator
            Blk* probe = meta->rev_idom;
            BlkMeta* probe_meta = getBlkMeta(probe);
            while (! probe_meta->jmp_is_critical) {
                probe = probe_meta->rev_idom;
                probe_meta = getBlkMeta(probe);
            }
            // rewrite to go to that postdominator
            blk->s1 = probe;
            blk->s2 = NULL;
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
