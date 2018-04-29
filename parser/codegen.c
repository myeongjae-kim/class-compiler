/* codgen.c       Generate Assembly Code for x86         11 Jan 18   */
// TODO: AREFOP, POINTEROP, make it correct. I can see the offset!

/* Copyright (c) 2018 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "symtab.h"
#include "lexan.h"
#include "genasm.h"
#include "codegen.h"

#include <assert.h>
/** #define assert(x);  */

void genc(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */

void gencode(TOKEN pcode, int varsize, int maxlabel)
  {  TOKEN name, code;
     name = pcode->operands;
     code = name->link->link;
     nextlabel = maxlabel + 1;
     stkframesize = asmentry(name->stringval,varsize);
     genc(code);
     asmexit(name->stringval);
  }

/* Trivial version: always returns RBASE + 0 */
/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */

#define REG_NUM (XMM7 + 1)
int reg_table[REG_NUM]; // EAX ECX EDX EBX ... XMM7

int getreg(int kind) {
  /*     ***** fix this *****   */
  int i = 0;

  // integer
  if (kind == WORD) {
    for(i = 0; i <= EBX; i++) {
      if (reg_table[i] == 0) {
        reg_table[i] = 1;
        return i;
      }
    }
    // full of register
    assert(0);

  } else if (kind == FLOAT) {
    for(i = XMM0; i <= XMM7; i++) {
      if (reg_table[i] == 0) {
        reg_table[i] = 1;
        return i;
      }
    }

    // full of register
    assert(0);
  } else {
    //????
    assert(0);
  }

   return RBASE;
}

void relreg(int reg) {
  reg_table[reg] = 0;
}

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code) {
  int num, reg, i;
  int reg1, reg2;
  int is_reg1_int = 1;
  int is_reg2_int = 1;

  int regary[8];
  int saved_regs[8], j, k;

  double f_num;
  TOKEN tok, args;

  if (DEBUGGEN) {
    printf("genarith\n");
    dbugprinttok(code);
  }

  switch ( code->tokentype )
  {
    case NUMBERTOK:
      switch (code->basicdt) {
        case INTEGER:
          num = code->intval;
          reg = getreg(WORD);
          if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE ) {
            if (code->symtype && code->symtype->size == 8) {
              asmimmed(MOVQ, num, reg);
            } else {
              asmimmed(MOVL, num, reg);
            }
          }
          break;
        case REAL:
          f_num = code->realval;
          num = nextlabel++;
          makeflit(f_num, num);

          reg = getreg(FLOAT);
          asmldflit(MOVSD, num, reg);
          break;
      }
      break;

    case STRINGTOK:
      num = nextlabel++;
      makeblit(code->stringval, num);

      if (reg_table[EDI]) {
        assert(0);
      }
      reg_table[EDI] = 1;
      reg = EDI;

      asmlitarg(num, reg);
      break;

    case IDENTIFIERTOK:
      /*     ***** fix this *****   */
      // Load value from memory to register
      
      if (!code->symentry) {
        code->symentry = searchst(code->stringval);
      }

      if (!code->symtype) {
        code->symtype = code->symentry->datatype;
      }

      // Integer
      if (strcmp(code->symtype->namestring, "integer") == 0) {
        reg = getreg(WORD);
        asmld(MOVL, code->symentry->offset - stkframesize, reg, code->stringval);
        // Real
      } else if (strcmp(code->symtype->namestring, "real") == 0) {
        reg = getreg(FLOAT);
        asmld(MOVSD, code->symentry->offset - stkframesize, reg, code->stringval);
      } else {
        /** assert(0); */
        reg = getreg(WORD);
        asmld(MOVQ, code->symentry->offset - stkframesize, reg, code->stringval);
      }
      // TODO: Other types

      
      break;
    case OPERATOR:
      switch(code->whichval) {
        case PLUSOP:
        case MINUSOP:
        case TIMESOP:
        case DIVIDEOP:
        case DIVOP:
        case MODOP:
          tok = code->operands;
          reg1 = genarith(tok);


          if (tok->link == NULL) {
            if (EAX <= reg1 && reg1 <= EBX) {
              is_reg1_int = 1;
            } else {
              is_reg1_int = 0;
            }

            // when # of operands is 1
            switch(code->whichval) {
              case MINUSOP:
                // negation
                if (is_reg1_int) {
                  // integer
                  asmr(NEGL, reg1);
                } else {
                  // float
                  reg2 = getreg(FLOAT);
                  asmfneg(reg1, reg2);
                  relreg(reg2);
                }
                break;
              default:
                break;
                // do nothing
            }
          } else {
            // when # of operands is 2
            tok = tok->link;
            reg2 = genarith(tok);

            if (tok->whichval == FUNCALLOP) {
              int temp = reg1;
              reg1 = reg2;
              reg2 = temp;
            } else if (tok->whichval == AREFOP) {
              int temp = getreg(WORD);
              if (tok->symtype->size == 4) {
                // assume that symtype == basictype
                asmldr(MOVL, tok->operands->link->intval, reg2, temp, "^.");
              } else {
                asmldr(MOVQ, tok->operands->link->intval, reg2, temp, "^.");
              }
              relreg(reg2);
              reg2 = temp;
              /** assert(0); */
            }


            if (EAX <= reg1 && reg1 <= EBX) {
              is_reg1_int = 1;
            } else {
              is_reg1_int = 0;
            }

            if (EAX <= reg2 && reg2 <= EBX) {
              is_reg2_int = 1;
            } else {
              is_reg2_int = 0;
            }

            if (is_reg1_int != is_reg2_int) {
              assert(0);
            }

            switch(code->whichval) {
              case PLUSOP:
                if (is_reg1_int) {
                  asmrr(ADDL, reg2, reg1);
                } else {
                  asmrr(ADDSD, reg2, reg1);
                }
                break;
              case MINUSOP:
                if (is_reg1_int) {
                  asmrr(SUBL, reg2, reg1);
                } else {
                  asmrr(SUBSD, reg2, reg1);
                }
                break;
              case TIMESOP:
                if (is_reg1_int) {
                  asmrr(IMULL, reg2, reg1);
                } else {
                  asmrr(MULSD, reg2, reg1);
                }
                break;
              case DIVOP:
              case DIVIDEOP:
                if (is_reg1_int) {
                  asmrr(DIVL, reg2, reg1);
                } else {
                  asmrr(DIVSD, reg2, reg1);
                }
                break;
              case MODOP:
                // no mod op;
                assert(0);
                break;
            }

            relreg(reg2);
          }

          reg = reg1;
          break;
          

        case FLOATOP:
          reg1 = genarith(code->operands);
          reg2 = getreg(FLOAT);
          asmfloat(reg1, reg2);

          relreg(reg1);
          reg = reg2;
          break;

        case FIXOP:
          reg1 = genarith(code->operands);
          reg2 = getreg(WORD);
          asmfix(reg1, reg2);

          relreg(reg1);
          reg = reg2;
          break;

        case FUNCALLOP:
          // CALLER
          tok = code->operands; // FUNCTION NAME IDENTIFIER

          args = tok->link; // first argument

          // int arg -> can be used to three. EAX, ECX, EDX
          // float arg -> can be used to one. XMM0

          // Save used registers before calling
          // No need to store integer registers. only float registers...why?
          

          j = 0;
          // Make integer saved.
          /*
          for(i = EAX, j = 0; i <= EDX; i++) {
            if(reg_table[i] == 1) {
              asmsttemp(i);
              saved_regs[j] = i;
              relreg(i);
              j++;
            }
          }
          */

          // Make float saved.
          for(i = XMM0; i <= XMM7; i++) {
            if(reg_table[i] == 1) {
              asmsttemp(i);
              saved_regs[j] = i;
              relreg(i);
              j++;
            }
          }

          for(i = 0; args; i++) {
            regary[i] = genarith(args);
            if (args->tokentype == OPERATOR &&
                args->whichval == AREFOP) {
              // assume that it is '^. '
              TOKEN offset = args->operands->link;

              /** if (strcmp(rhs->symtype->namestring, "integer") == 0) { */
              if (args->symtype->basicdt == INTEGER) {
                int i_dst = getreg(WORD);
                asmldr(MOVL, offset->intval, regary[i], i_dst, "^.");
                relreg(regary[i]);
                regary[i] = i_dst;
              /** } else if (strcmp(rhs->symtype->namestring, "real") == 0) { */
              } else if (args->symtype->basicdt == REAL) {
                int f_dst = getreg(FLOAT);
                asmldr(MOVSD, offset->intval, regary[i], f_dst, "^.");
                relreg(regary[i]);
                regary[i] = f_dst;
              } else if (args->symtype->basicdt == POINTER) {
                int i_dst = getreg(WORD);
                asmldr(MOVQ, offset->intval, regary[i], i_dst, "^.");
                relreg(regary[i]);
                regary[i] = i_dst;
              } else {
                assert(0);
              }
            }


            args = args->link;

            if (regary[i] == EBX || regary[i] > XMM0) {
              // too many arguments
              assert(0);
            }
          }

          // call function
          if (strcmp(tok->stringval, "new") == 0
              || strcmp(tok->stringval, "writelni") == 0) {
            asmrr(MOVL, EAX, EDI);
          } else if (strcmp(tok->stringval, "writelnf") == 0) {
          
          }
          asmcall(tok->stringval);

          // TODO release all regs except first (return)
          // If used reg is integer, release other regs
          // If used reg is float, release other floats
          reg = regary[0];
          /** assert(0); */

          // Restore registers
          // just restore return value to empty register.
          // TODO I think it will be wrong...
          for(i = 0, k = 0; i < j; i++) {
            if (saved_regs[i] <= EDX) {
              assert(0); // no saved integers
              break;
            } else if (XMM0 <= saved_regs[i] && saved_regs[i] <= XMM7){
              reg1 = getreg(FLOAT);
              asmldtemp(reg1);
              reg = reg1;
              break;
            } else {
              assert(0);
            }
          }


          break;

        case AREFOP:
          if (code->operands->whichval == POINTEROP) {
            reg = genarith(code->operands);
          } else {
            reg = genarith(code->operands->link);
            asmop(CLTQ);
          }
          break;

        case POINTEROP:
          reg = genarith(code->operands);
          if (code->operands->whichval == AREFOP) {
            tok = code->operands->operands->link; // tok has offset
            reg1 = getreg(WORD);
            asmldr(MOVQ, tok->intval, reg, reg1, "^.");
            relreg(reg);
            reg = reg1;
          } else {
            // do nothing?
          }
          break;
        default:
          assert(0);
      }
      break;

  }
  return reg;
}

void gen_jump(int opval, int labeln) {
  switch (opval) {
    case EQOP:
      asmjump(JE, labeln);
      break;
    case NEOP:
      asmjump(JNE, labeln);
      break;
    case LTOP:
      asmjump(JL, labeln);
      break;
    case LEOP:
      asmjump(JLE, labeln);
      break;
    case GEOP:
      asmjump(JGE, labeln);
      break;
    case GTOP:
      asmjump(JG, labeln);
      break;
    default:
      assert(0);
      break;
  }
}


/* Generate code for a Statement from an intermediate-code form */
// code must be operator tok
void genc(TOKEN code) {
  TOKEN tok, lhs, rhs, false_tok;
  int reg, offs, label1, label2;
  int reg_lhs;
  SYMBOL sym;

  int regary[8];

  if (DEBUGGEN) {
    printf("genc\n");
    dbugprinttok(code);
  }

  if ( code->tokentype != OPERATOR ) {
    printf("Bad code token");
    dbugprinttok(code);
  }

  switch ( code->whichval ) {
    case PROGNOP:
      tok = code->operands;
      while ( tok != NULL ) {
        genc(tok);
        tok = tok->link;
      }
      break;
    case ASSIGNOP:                   /* Trivial version: handles I := e */
      lhs = code->operands;
      rhs = lhs->link;

      if(lhs->symtype &&
          lhs->symtype->size == 8) {
        /** assert(rhs->tokentype == NUMBERTOK); */
        if (rhs->symtype == NULL) {
          rhs->symtype = lhs->symtype;
        }
        if (rhs->symentry == NULL) {
          rhs->symentry = searchst(rhs->stringval);
        }
      }

      reg = genarith(rhs);              /* generate rhs into a register */
      // when rhs is aref
      if (rhs->whichval == AREFOP) {
        // assume that it is '^. '
        TOKEN offset = rhs->operands->link;

        /** if (strcmp(rhs->symtype->namestring, "integer") == 0) { */
        if (rhs->symtype->basicdt == INTEGER) {
          int i_dst = getreg(WORD);
          asmldr(MOVL, offset->intval, reg, i_dst, "^.");
          relreg(reg);
          reg = i_dst;
        /** } else if (strcmp(rhs->symtype->namestring, "real") == 0) { */
        } else if (rhs->symtype->basicdt == REAL) {
          int f_dst = getreg(FLOAT);
          asmldr(MOVSD, offset->intval, reg, f_dst, "^.");
          relreg(reg);
          reg = f_dst;
        } else if (rhs->symtype->basicdt == POINTER) {
          int i_dst = getreg(WORD);
          asmldr(MOVQ, offset->intval, reg, i_dst, "^.");
          relreg(reg);
          reg = i_dst;
        } else {
          assert(0);
        }
      }
      

      //sym = lhs->symentry;              /* assumes lhs is a simple var  */
      if(lhs->tokentype == IDENTIFIERTOK) {
        sym = searchst(lhs->stringval);    /* assumes lhs is a simple var  */
        offs = sym->offset - stkframesize; /* net offset of the var   */
        switch (code->basicdt) {           /* store value into lhs  */
          case INTEGER:
            if(sym->size == 8) {
              asmst(MOVQ, reg, offs, lhs->stringval); // MOVL is for ASSIGNOP
            } else {
              asmst(MOVL, reg, offs, lhs->stringval); // MOVL is for ASSIGNOP
            }
            break;

          case REAL:
            asmst(MOVSD, reg, offs, lhs->stringval); // MOVSD is for ASSIGNOP
            break;
          default:
            assert(0);
            /* ...  */
        }
      } else {
        // assume that lhs is aref

	//movl	%eax,32(%rcx)         	#  %eax -> ^.  [32+%rcx]

        reg_lhs = genarith(lhs);

        tok = lhs->operands->link; // offset of lhs;

        switch (code->basicdt) {           /* store value into lhs  */
          case INTEGER:
            /** if(code->operands->link->symentry */
            /**   && code->operands->link->symentry->size == 8) { */
            if(lhs->symtype->size == 8) {

              if (lhs->operands->tokentype == OPERATOR) {
                // It's only for pointer
                asmstr(MOVQ, reg, tok->intval, reg_lhs, "^. "); // TODO.
              } else {
                asmstrr(MOVQ, reg,
                    lhs->operands->symtype->offset - stkframesize,
                    reg_lhs,
                    lhs->operands->stringval);
              }

            } else {

              if (lhs->operands->tokentype == OPERATOR) {
                // It's only for pointer
                asmstr(MOVL, reg, tok->intval, reg_lhs, "^. "); // TODO.
              } else {
                asmstrr(MOVL, reg,
                    lhs->operands->symtype->offset - stkframesize,
                    reg_lhs,
                    lhs->operands->stringval);
              }

            }
            break;

          case REAL:
            if (lhs->operands->tokentype != OPERATOR ||
                lhs->operands->whichval != POINTEROP) {
              // lhs is aref
              asmstrr(MOVSD, reg,
                  lhs->operands->symtype->offset  - stkframesize,
									reg_lhs,
									lhs->operands->stringval
                  );
            } else {
              if (lhs->operands->tokentype == OPERATOR) {
                // It's only for pointer
                asmstr(MOVSD, reg, tok->intval, reg_lhs, "^. "); // TODO.
              } else {
                asmstrr(MOVSD, reg,
                    lhs->operands->symtype->offset - stkframesize,
                    reg_lhs,
                    lhs->operands->stringval);
              }
						}




            break;
          default:
            assert(0);
            /* ...  */
        }


        
        relreg(reg_lhs);
      }

      relreg(reg);
      break;
    case LABELOP:
      tok = code->operands;
      asmlabel(tok->intval);
      break;
    case IFOP:
      tok = code->operands;      // comparing statement
      genc(tok); 

      // jmp when condition is true
      label1 = nextlabel++;
      gen_jump(tok->whichval, label1);

      // If it is false, do false code
      false_tok = tok->link->link;
      if (false_tok) {
        genc(false_tok);
      }

      // and exit the loop
      label2 = nextlabel++;
      asmjump(JMP, label2);


      asmlabel(label1);
      // If cmpl is true
      tok = tok->link;
      genc(tok);

      // If cmpl is false
      asmlabel(label2);

      break;
    case EQOP:
    case NEOP:
    case LTOP:
    case LEOP:
    case GEOP:
    case GTOP:
      lhs = code->operands;
      rhs = lhs->link;

      regary[0] = genarith(lhs);

      if (rhs->symtype == NULL) {
        rhs->symtype = lhs->symtype;
      }

      regary[1] = genarith(rhs);

      if (lhs->symtype->size == 8) {
        asmrr(CMPQ, regary[1], regary[0]);
      } else {
        asmrr(CMPL, regary[1], regary[0]);
      }

      relreg(regary[0]);
      relreg(regary[1]);
      break;
    case FUNCALLOP:
      regary[0] = genarith(code);
      relreg(regary[0]);
      break;
    case GOTOOP:
      tok = code->operands;
      asmjump(JMP, tok->intval);
      break;
  }
}
