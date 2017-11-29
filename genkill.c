/*
 * =====================================================================================
 *
 *       Filename:  genkill.c
 *
 *    Description:  Program
 *
 *        Version:  1.0
 *        Created:  11/07/2017 11:20:55 PM
 *       Revision:  none
 *       Compiler:  gcc
 *
 *         Author:  Artem Abramov (aa), tematibr@gmail.com
 *   Organization:  
 *
 * =====================================================================================
 */


// how to
/*
 * book section 9.2 (in book page 604), but the figure is broken
 * The good figure 9.13 is here:
 * http://www.brainkart.com/media/extra/sf0NBSg.jpg
 *
 * Also a pretty good presentation here (in browser pages 15 and 16)
 * http://www.eecs.umich.edu/courses/eecs583/slides/Lecture5.pdf
 *
 * Gen kill happen before reaching definitions. Input for reaching definitions
 * is gen-kill of all blocks.
 *
 * Dragon book is at:
 * okular '/home/artem/Desktop/Broad-dev-books/Code Architecture Books HowTo/Compilers Principles Techniques and Tools.pdf'
 *
 * Run gdb of gen-kill with:
 * gdb -ex 'set args -path /home/artem/Desktop/Uni/ispran/homework/ < data.txt' gk
 *
 * i->to = instruction->assigned_to_variable (assign target)
 * to.val = value of the variable, its key?
 * And then we look up the temporary in the tmp[...] by the key to.val thus we find the description for the temporary
 */


#include <qbe/all.h>
#include <stdio.h>
#include <stdbool.h>

static void readfn (Fn *fn);
static void readdat (Dat *dat);

static void readfn (Fn *fn) {
  for (Blk *blk = fn->start; blk; blk = blk->link) {
    // arrays contain to.val
    int gen_count = 0;
    unsigned int genvars[blk->nins];
    printf("@%s", blk->name);
    printf("\n\tgen =");

    // Tmp0 is the start of temporaries container, it starts at array index 64, before that go Rxxx
    for (Ins* i=blk->ins; i-blk->ins < blk->nins; i++) {
        // if we are assigning to a temporary variable and not elsewhere
        if (Tmp0 <= i->to.val) {
            char* s1 = fn->tmp[i->to.val].name;
            bool uniq = true;
            for (int i=0; i<gen_count; i++) {
                if (strcmp(fn->tmp[genvars[i]].name, s1) == 0){
                    uniq = false;
                    break;
                }
            }
            if (! uniq) {
                continue;
            }
            genvars[gen_count++] = i->to.val;
            // then we are GEN the variable in this block
            printf(" @%s%%%s", blk->name, s1);
        }
    }

    printf("\n\tkill =");

    // count down from gen_count
    while (gen_count-- > 0) {
        // search where we might be KILL this variable
        // iterate over all other blocks and instructions
        char* s2 = fn->tmp[genvars[gen_count]].name;
        for (Blk *blk_other = fn->start; blk_other; blk_other = blk_other->link) {
            int blkkqty = 0;
            char* blkk[blk_other->nins];
            // this is the same block as current
            if (blk_other == blk) {
                continue;
            }
            for (Ins* i_other=blk_other->ins; i_other-blk_other->ins < blk_other->nins; i_other++) {
                // the other instruction assigns to the same variable
                char* s1 = fn->tmp[i_other->to.val].name;
                if (strcmp(s1, s2) != 0) {
                    continue;
                }
                bool uniq = true;
                for (int i=0; i<blkkqty; i++) {
                    if (strcmp(blkk[i], s1) == 0){
                        uniq = false;
                        break;
                    }
                }
                if (! uniq) {
                    continue;
                }
                blkk[blkkqty++] = s1;
                // then we killed that instruction, that assigned to the same variable
                printf(" @%s%%%s", blk_other->name, s1);
            }
        }
    }
    printf("\n");
  }
  printf("\n");
}

static void readdat (Dat *dat) {
  (void) dat;
}

int main () {
  parse(stdin, "<stdin>", readdat, readfn);
  freeall();
}
