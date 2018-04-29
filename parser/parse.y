%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 30 Jul 13   */

/* Copyright (c) 2013 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

void instvars(TOKEN idlist, TOKEN typetok);
TOKEN check_const(TOKEN id);
TOKEN const_findtype(TOKEN id);
TOKEN nil_to_zero(TOKEN id);
TOKEN optimize_progn(TOKEN progn_tok);

#define MAX_LABEL 1024
int labels[MAX_LABEL];

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE
%%

program    :  PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON lblock DOT
                { $1->tokentype = OPERATOR;
                  $1->whichval = PROGRAMOP;
                  $1->operands = makeprogram($2, makeprogn($3, $4), $7);
                  parseresult = $1; }
             ;
  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expression THEN statement ELSE statement
                                       { $$ = makeif($1, $2, $4, $5); }
             |  IF expression THEN statement  %prec LOWER_THAN_ELSE
                                       { $$ = makeif($1, $2, $4, NULL); }
             |  variable ASSIGN expression { $$ = binop($2, $1, $3); }
             |  funcall
             |  WHILE expression DO statement 
                                           { $$ = makewhile($1, $2, $3, $4); }
             |  REPEAT statement_list UNTIL expression
                                         { 
                                           TOKEN opt = NULL;
                                           $$ = makerepeat($1, $2, $3, $4);
                                           $$ = makeprogn($1, $$);

                                           opt = optimize_progn($$);
                                           $$ = opt ? opt : $$;
                                         }
             |  FOR IDENTIFIER ASSIGN expression TO expression DO statement
                       {
                         $$ = makefor(1, $1,
                                        binop($3, $2, $4), $5, $6, $7, $8);
                         $$ = makeprogn($1, $$);
                       }
             |  FOR IDENTIFIER ASSIGN expression DOWNTO expression DO statement
                       {
                         $$ = makefor(-1, $1,
                                        binop($3, $2, $4), $5, $6, $7, $8);
                         $$ = makeprogn($1, $$);
                       }
             |  GOTO NUMBER { $$ = dogoto($1, $2); }
             |  label
             ;
  statement_list :  statement SEMICOLON statement_list { $$ = cons($1, $3); }
                 |  statement
                 ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  term       :  term times_op factor              { $$ = binop($2, $1, $3); }
             |  factor
             ;
  unsigned_constant : IDENTIFIER {check_const($1);}
                    | NUMBER 
                    | NIL        { $$ = nil_to_zero($1); }
                    | STRING
                    ;
  sign       :  PLUS
             |  MINUS
             ;
  constant   :  sign IDENTIFIER   { $$ = const_findtype($2);
                                    $$ = unaryop($1, $$);    }
             |  IDENTIFIER        { $$ = const_findtype($1); }
             |  sign NUMBER       { $$ = const_findtype($2);
                                    $$ = unaryop($1, $$);    }
             |  NUMBER            { $$ = const_findtype($1); }
             |  STRING            { $$ = const_findtype($1); }
             ;
  id_list    :  IDENTIFIER COMMA id_list       { $$ = cons($1, $3); }
             |  IDENTIFIER                     { $$ = cons($1, NULL); }
             ; 
  simple_type:  IDENTIFIER                     { $$ = findtype($1); }
             |  LPAREN id_list RPAREN          { $$ = instenum($2); }
             |  constant DOTDOT constant       { $$ = instdotdot($1, $2, $3); }
             ;
  simple_type_list : simple_type COMMA simple_type_list { $$ = cons($1, $3); }
                   | simple_type                        {$$ = cons($1, NULL);}
                   ;
  fields     :  id_list COLON type          { $$ = instfields($1, $3); }
             ;
  field_list :  fields SEMICOLON field_list { $$ = cons($1, $3); }
             |  fields
             ;
  type       :  simple_type
             |  ARRAY LBRACKET simple_type_list RBRACKET OF type
                                            { $$ = instarray($3, $6); }
             |  RECORD field_list END       { $$ = instrec($1, $2); }
             |  POINT IDENTIFIER            { $$ = instpoint($1, $2); }
             ;
  plus_op    :  PLUS | MINUS | OR              
             ;
  simple_expression : sign term             { $$ = unaryop($1, $2); }
                    | term
                    | simple_expression plus_op term
                                            { $$ = binop($2, $1, $3); } 
                    ;
  compare_op :  EQ | LT | GT | NE | LE | GE | IN      
             ;
  expression :  expression compare_op simple_expression
                                                { $$ = binop($2, $1, $3); }
             |  simple_expression
             ;
  expr_list  :  expression COMMA expr_list  { $$ = cons($1, $3); }
             |  expression
             ;
  variable   :  IDENTIFIER        
             |  variable LBRACKET expr_list RBRACKET
                                           { $$ = arrayref($1, $2, $3, $4); }
             |  variable DOT IDENTIFIER    { $$ = reducedot($1, $2, $3); }
             |  variable POINT             { $$ = dopoint($1, $2); }
             ;
  funcall    :  IDENTIFIER LPAREN expr_list RPAREN 
                                            { $$ = makefuncall($2, $1, $3); }
  factor     :  unsigned_constant
             |  variable
             |  funcall
             |  LPAREN expression RPAREN    { $$ = $2; }
             |  NOT factor
             ;
  times_op   :  TIMES | DIVIDE | DIV | MOD | AND
             ;
  numlist    :  NUMBER COMMA numlist         { $$ = cons($1, $3); }
             |  NUMBER
             ;
  ldef_list  :  numlist SEMICOLON           { instlabel($1); }
             ;
  lblock     :  LABEL ldef_list cblock 
                                            { $$ = $3; }
             |  cblock
             ;
  cblock     :  CONST cdef_list tblock { $$ = $3; }
             |  tblock
             ;
  cdef       :  IDENTIFIER EQ constant       { instconst($1, $3); }
             ;
  cdef_list  :  cdef SEMICOLON cdef_list
             |                    { $$ = NULL; } 
             ;
  tblock     :  TYPE tdef_list vblock { $$ = $3; }
             |  vblock
             ;
  tdef       :  IDENTIFIER EQ type           { insttype($1, $3); }
             ;
  tdef_list  :  tdef SEMICOLON tdef_list
             |                    { $$ = NULL; }
             ;
  vblock     :  VAR vdef_list block   { $$ = $3; }
             |  block
             ;
  vdef       :  id_list COLON type         { instvars($1, $3); }
             ;
  vdef_list  :  vdef SEMICOLON vdef_list
             |                    { $$ = NULL; }
             ;
  block      :  BEGINBEGIN statement endpart
                                  { $$ = makeprogn($1,cons($2, $3)); 
                                    TOKEN opt = optimize_progn($$);
                                    $$ = opt ? opt : $$;
                                  }
             ;
  label      :  NUMBER COLON statement  
                                  { $$ = dolabel($2, $1, $3); }
             ;

%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        31             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

 int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { SYMBOL lhs_sym = searchst(lhs->stringval); // type of token
    SYMBOL rhs_sym = searchst(rhs->stringval); // type of token

    SYMBOL real_sym = searchst("real");
    SYMBOL int_sym = searchst("integer");

    TOKEN coerce_tok = NULL;

    if(lhs->tokentype == OPERATOR) {
      lhs_sym = lhs->symtype;
    }
    if(rhs->tokentype == OPERATOR) {
      rhs_sym = rhs->symtype;
    }

    op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */

    // operator's return type.
    if(!lhs_sym && lhs->basicdt == INTEGER) {
      op->symtype = int_sym;
      op->basicdt = INTEGER;
    } else if (!lhs_sym && lhs->basicdt == REAL) {
      op->symtype = real_sym;
      op->basicdt = REAL;
    } else if (lhs_sym 
                && lhs_sym == int_sym || lhs_sym->datatype == int_sym) {
      op->symtype = int_sym;
      op->basicdt = INTEGER;
    } else if (lhs_sym 
                && lhs_sym == real_sym || lhs_sym->datatype == real_sym) {
      op->symtype = real_sym;
      op->basicdt = REAL;
    }

    // Coercion Case.
    switch (op->whichval) {
      case PLUSOP:
      case MINUSOP:
      case OROP:

      case TIMESOP:
      case DIVIDEOP:
      case DIVOP:
      case MODOP:
      case ANDOP:


      case EQOP:
      case LTOP:
      case GTOP:
      case NEOP:
      case LEOP:
      case GEOP:
      case INOP:


        if(DEBUG) printf("\t\t\tplus_op\n");

        // both are number constant
        if (!lhs_sym && !rhs_sym) {
          if(lhs->basicdt == INTEGER && rhs->basicdt == REAL) {
            // need to coerce
            lhs->basicdt = REAL;
            lhs->realval = lhs->intval;
            op->symtype = real_sym;

          } else if(lhs->basicdt == REAL && rhs->basicdt == INTEGER) {
            // need to coerce
            rhs->basicdt = REAL;
            rhs->realval = rhs->intval;
            op->symtype = real_sym;

          } else {
            // do nothing
            // no need to coerce
          }
        } else if (lhs_sym && !rhs_sym) {
          // lhs is symbol constant
          if( (lhs_sym == int_sym || lhs_sym->datatype == int_sym)
                && rhs->basicdt == REAL) {
            // need to coerce
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;
            coerce_tok->basicdt = REAL;

            coerce_tok->operands = lhs;
            coerce_tok->link = lhs->link;
            lhs->link = NULL;

            op->operands = coerce_tok;

            op->symtype = real_sym;
          } else if( (lhs_sym == real_sym || lhs_sym->datatype == real_sym)
                && rhs->basicdt == INTEGER) {
            // need to coerce
            rhs->basicdt = REAL;
            rhs->realval = rhs->intval;

            op->symtype = real_sym;
          } else {
            // do nothing
            // no need to coerce
          }
        } else if (!lhs_sym && rhs_sym) {
          // rhs is symbol constant
          if(lhs->basicdt == INTEGER 
             && (rhs_sym == real_sym || rhs_sym->datatype == real_sym)) {
            // need to coerce
            lhs->basicdt = REAL;
            lhs->realval = lhs->intval;

            op->symtype = real_sym;
          } else if(lhs->basicdt == REAL 
            && (rhs_sym == int_sym || rhs_sym->datatype == int_sym)) {
            // need to coerce
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;
            coerce_tok->basicdt = REAL;

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = real_sym;
          } else {
            // do nothing
            // no need to coerce
          }
        } else {
          // both are symbol constant
          if((lhs_sym == int_sym || lhs_sym->datatype == int_sym)
            && (rhs_sym == real_sym || rhs_sym->datatype == real_sym)) {
            // need to coerce
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;
            coerce_tok->basicdt = REAL;

            coerce_tok->operands = lhs;
            coerce_tok->link = lhs->link;
            lhs->link = NULL;

            op->symtype = real_sym;
          } else if((lhs_sym == real_sym || lhs_sym->datatype == real_sym)
            && (rhs_sym == int_sym || rhs_sym->datatype == int_sym)) {
            // need to coerce
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;
            coerce_tok->basicdt = REAL;

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = real_sym;
          } else {
            // do nothing
            // no need to coerce
          }
        }
        break;

      case ASSIGNOP:
        if (DEBUG) printf("\t\t\tassignop\n");
        // TODO : lhs must be variable(= identifier)
        

        // left is integer and right is real
        if (lhs_sym == int_sym || lhs_sym->datatype == int_sym){

          // rhs is constant
          if(!rhs_sym && rhs->basicdt == REAL) {
            rhs->basicdt = INTEGER;
            rhs->intval = rhs->realval;
            op->symtype = int_sym;
            op->basicdt = INTEGER;

          // rhs is not a constant
          } else if (rhs_sym == real_sym
                      || (rhs_sym && rhs_sym->datatype == real_sym)) {
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FIXOP;
            coerce_tok->symtype = int_sym;
            coerce_tok->basicdt = INTEGER;

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = int_sym;
            op->basicdt = INTEGER;
          }

        // left is real and right is integer
        } else if (lhs_sym == real_sym || lhs_sym->datatype == real_sym){

          // rhs is constant
          if(!rhs_sym && rhs->basicdt == INTEGER) {
            rhs->basicdt = REAL;
            rhs->realval = rhs->intval;
            op->symtype = real_sym;
            op->basicdt = REAL;

          // rhs is not a constant
          } else if (rhs_sym == int_sym
                      || (rhs_sym && rhs_sym->datatype == int_sym)) {
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;
            coerce_tok->basicdt = REAL;

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = real_sym;
            op->basicdt = REAL;
          }
        }


        break;
      
      /* case EQOP:
       * case LTOP:
       * case GTOP:
       * case NEOP:
       * case LEOP:
       * case GEOP:
       * case INOP:
       *   if (DEBUG) printf("\t\t\tcompare op\n");
       *   // TODO
       *   break;
       *  */

      deafult:
        if (DEBUG) printf("\t\t\t Token not found. op->whichval: %d\n",
                                                              op->whichval);
    }



    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };

    return op;
  }

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };

     return tok;
   }

TOKEN findtype(TOKEN tok) {
  SYMBOL found_type = searchst(tok->stringval);
  tok->symtype = found_type;

  if (DEBUG) {
    printf("findtype\n");
    dbugprinttok(tok);
  }
  return tok;
}

TOKEN const_findtype(TOKEN tok) {
  switch(tok->basicdt) {
    case INTEGER:
      tok->symtype = searchst("integer");
      break;
    case REAL:
      tok->symtype = searchst("real");
      break;
    case STRINGTYPE:
      tok->symtype = searchst("char");
      break;
    case BOOLETYPE:
      tok->symtype = searchst("boolean");
      break;
    case POINTER:
      /* TODO */
      break;
    default:
      break;
  }
  return tok;
}

/* install variables in symbol table */
void instvars(TOKEN idlist, TOKEN typetok) {
  SYMBOL sym, typesym; int align;
  typesym = typetok->symtype;
  align = alignsize(typesym);
  while ( idlist != NULL) { /* for each id */
    sym = insertsym(idlist->stringval);
    sym->kind = VARSYM;
    sym->offset =      /* "next */
        wordaddress(blockoffs[blocknumber], align);
    sym->size = typesym->size;
    blockoffs[blocknumber] = /* "next" */
                        sym->offset + sym->size;
    sym->datatype = typesym;
    sym->basicdt = typesym->basicdt;
    idlist = idlist->link;
  }

  if (DEBUG) {
    printf("instvars\n");
    dbugprinttok(idlist);
    dbugprinttok(typetok);
  }

}

TOKEN optimize_progn(TOKEN progn_tok) {
  // TODO
  return progn_tok;
  
  int is_optimized = 0;
  // optimize
  if (progn_tok->operands->tokentype == OPERATOR
        && progn_tok->operands->whichval == PROGNOP) {

    progn_tok = progn_tok->operands;

    TOKEN link_iter = progn_tok->operands;
    TOKEN link_iter_next = link_iter->link;

    while(link_iter_next != NULL) {
      link_iter = link_iter_next;
      link_iter_next = link_iter_next->link;
    }

    link_iter->link = progn_tok->link;
    progn_tok->link = NULL;

    is_optimized = 1;
  }

  if (progn_tok->operands->link
      && progn_tok->operands->link->tokentype == OPERATOR
      && progn_tok->operands->link->whichval == PROGNOP) {


    TOKEN link_iter = progn_tok->operands->link->operands;
    TOKEN link_iter_next = link_iter->link;

    while(link_iter_next != NULL) {
      link_iter = link_iter_next;
      link_iter_next = link_iter_next->link;
    }

    link_iter->link = progn_tok->operands->link->link;
    progn_tok->operands->link->link = NULL;

    progn_tok->operands->link = progn_tok->operands->link->operands;

    is_optimized = 1;
  }

  return is_optimized ? progn_tok : NULL;
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement){

  TOKEN label = makelabel();
  asg->link = label;

  TOKEN if_token = tokb;
  if_token->tokentype = OPERATOR;
  if_token->whichval = IFOP;

  label->link = if_token;

  // tokc = '<='
  TOKEN comp_token = tokc;
  comp_token->tokentype = OPERATOR;
  comp_token->whichval = sign == 1 ? LEOP : GEOP;

  if_token->operands = comp_token; 

  comp_token->operands = (TOKEN)talloc();
  memcpy(comp_token->operands, asg->operands, sizeof(*comp_token->operands));
  comp_token->operands->link = endexpr;

  comp_token->link = makeprogn(talloc(), statement);


  TOKEN count_assign = (TOKEN)talloc();
  count_assign->tokentype = OPERATOR;
  count_assign->whichval = ASSIGNOP;

// after funcall
  count_assign->operands = (TOKEN)talloc();
  memcpy(count_assign->operands, comp_token->operands,
    sizeof(*count_assign->operands));
  
  TOKEN left_i = count_assign->operands;
  TOKEN inc = (TOKEN)talloc();

  left_i->link = inc;
  inc->tokentype = OPERATOR;
  inc->whichval = sign == 1 ? PLUSOP : MINUSOP; 

  TOKEN second_left_i = (TOKEN)talloc();
  memcpy(second_left_i, comp_token->operands, sizeof(*second_left_i));

  inc->operands = second_left_i;
  second_left_i->link = (TOKEN)talloc();
  second_left_i->link->tokentype = NUMBERTOK;
  second_left_i->link->basicdt = INTEGER;
  second_left_i->link->intval = 1;

// funcall's link is count_assign

  statement->link = count_assign;

// goto

  count_assign->link = makegoto(label->operands->intval);


  // optimize

  TOKEN opt_return = optimize_progn(if_token->operands->link);
  if (opt_return) {
    if_token->operands->link = opt_return;
  }

  if (DEBUG) {
    printf("makefor\n");
    dbugprinttok(tok);
    dbugprinttok(asg);
    dbugprinttok(tokb);
    dbugprinttok(endexpr);
    dbugprinttok(tokc);
    dbugprinttok(statement);
  }

  return asg;
}

TOKEN makenewfuncall(TOKEN asg, TOKEN fn_name, TOKEN args) {
  asg->tokentype = OPERATOR;
  asg->whichval = ASSIGNOP;
  asg->operands = args;

  TOKEN funcall = (TOKEN)talloc();
  funcall->tokentype = OPERATOR;
  funcall->whichval = FUNCALLOP;

  args->link = funcall;

  funcall->operands = fn_name;

  TOKEN size = (TOKEN)talloc();
  size->tokentype = NUMBERTOK;
  size->basicdt = INTEGER;
  size->symtype = searchst("integer");

  SYMBOL iter = searchst(args->stringval);
  while(iter->kind != POINTERSYM) {
    iter = iter->datatype;
  }

  size->intval = iter->datatype->size;

  fn_name->link = size;

  return asg;
}

TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  if (strcmp(fn->stringval, "new") == 0) {
    return makenewfuncall(tok, fn, args);
  }

  SYMBOL fn_sym = searchst(fn->stringval);

  tok->tokentype = OPERATOR;
  tok->whichval = FUNCALLOP;
  tok->operands = fn;
  fn->link = args;

  //return type should be in tok.
  tok->symtype = fn_sym->datatype->datatype;

  // coerce write function
  if(strcmp(fn->stringval, "write") == 0
      || strcmp(fn->stringval, "writeln") == 0) {
    int pos_idx = strlen(fn->stringval);

    if(args->symtype == NULL && args->tokentype != STRINGTOK) {
      args->symtype = searchst(args->stringval);
      if(args->symtype) {
        args->symtype = args->symtype->datatype;
      }
    }

    if(args->symtype &&
        strcmp(args->symtype->namestring, "integer") == 0) {
      fn->stringval[pos_idx] = 'i';
    } else if (args->symtype &&
        strcmp(args->symtype->namestring, "real") == 0) {
      fn->stringval[pos_idx] = 'f';
    }
  }


  if (DEBUG) {
    printf("makefuncall\n");
    dbugprinttok(tok);
    dbugprinttok(fn);
    dbugprinttok(args);
  }

  return tok;
}

TOKEN makelabel(void) {
  TOKEN tok = (TOKEN)talloc(), num_label = (TOKEN)talloc();

  tok->tokentype = OPERATOR;
  tok->whichval = LABELOP;

  num_label->tokentype = NUMBERTOK;
  num_label->basicdt = INTEGER;
  num_label->intval = labelnumber++;

  tok->operands = num_label;


  if (DEBUG) {
    printf("makelabel\n");
    dbugprinttok(tok);
    dbugprinttok(num_label);
  }

  return tok;
}

TOKEN makegoto(int label) {
  TOKEN tok = (TOKEN)talloc();
  tok->tokentype = OPERATOR;
  tok->whichval = GOTOOP;

  TOKEN label_tok = (TOKEN)talloc();
  label_tok->tokentype = NUMBERTOK;
  label_tok->basicdt = INTEGER;
  label_tok->intval = label;

  tok->operands = label_tok;

  if (DEBUG) {
    printf("makegoto\n");
    dbugprinttok(tok);
    dbugprinttok(label_tok);
  }

  return tok;
}


TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
  name->link = args;
  args->link = statements;

  if (DEBUG) {
    printf("makeprogram\n");
    dbugprinttok(name);
    dbugprinttok(args);
    dbugprinttok(statements);
  }

  return name;
}


/* instconst installs a constant in the symbol table */
void instconst(TOKEN idtok, TOKEN consttok) {
  SYMBOL sym = insertsym(idtok->stringval);
  sym->kind = CONSTSYM;
  sym->basicdt = consttok->basicdt;
  sym->datatype = consttok->symtype;

  // just copy memory regardless of basicdt.
  memcpy(sym->constval.stringconst, consttok->stringval,
                                      sizeof(sym->constval.stringconst));

  if(DEBUG) {
    printf("instconst\n");
    dbugprinttok(idtok);
    dbugprinttok(consttok);
  }

  return;
}

/* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
  TOKEN progn, if_token, empty_progn;


  TOKEN label = makelabel();

  progn = makeprogn(tokb, statements);

  label->link = progn;

  if_token = (TOKEN)talloc();

  progn->link = if_token;
  if_token->tokentype = OPERATOR;
  if_token->whichval = IFOP;

  if_token->operands = expr;

  empty_progn = (TOKEN)talloc();
  memset(empty_progn, 0, sizeof(*empty_progn));

  empty_progn->tokentype = OPERATOR;
  empty_progn->whichval = PROGNOP;
  /* if_token->link = empty_progn; */
  expr->link = empty_progn;

  empty_progn->link = makegoto(label->operands->intval);

  if (DEBUG) {
    printf("makerepeat\n");
    dbugprinttok(label);
    dbugprinttok(progn);
    dbugprinttok(if_token);
    dbugprinttok(empty_progn);
    dbugprinttok(empty_progn->link); // GOTO
  }

  return label;
}

TOKEN check_const(TOKEN id) {
  SYMBOL sym = searchst(id->stringval);

  if (DEBUG) {
    printf("check_const\n");
    dbugprinttok(id);
  }

  if (sym->kind == CONSTSYM) {
    id->tokentype = NUMBERTOK;
    id->basicdt = sym->basicdt;
    memcpy(id->stringval, sym->constval.stringconst,
                      sizeof(sym->constval.stringconst));
  }

  return id;
}

TOKEN unaryop(TOKEN op, TOKEN lhs) {
  op->operands = lhs;
  return op;
}


/* instlabel installs a user label into the label table */
void instlabel (TOKEN tok){
  if(tok->link) {
    instlabel(tok->link);
  }

  labels[labelnumber++] = tok->intval;
  tok = tok->link;
}


/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL typesym = searchins(typename->stringval);
  typesym->kind = TYPESYM;
  typesym->datatype = typetok->symtype;
  typesym->size = typesym->datatype->size;
  typesym->basicdt = typetok->basicdt;
}


/* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL pointsym = makesym(" ");
  pointsym->kind = POINTERSYM;

  pointsym->datatype = searchins(typename->stringval);
  pointsym->size = alignsize(pointsym);

  tok->symtype = pointsym;
  tok->basicdt = POINTER;
  return tok;
}

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type.  rectok is just a trash token to be
   used to return the result in its symtype */
TOKEN instrec(TOKEN rectok, TOKEN argstok) {
  SYMBOL recsym = makesym(" ");
  recsym->kind = RECORDSYM;

  rectok->symtype = recsym;

  TOKEN iter = argstok;
  SYMBOL prev_field = recsym;
  SYMBOL current_field = NULL;
  int offset = 0;
  int total_size = 0;
  int is_first = 1;
  while (iter != NULL) {
    current_field = makesym(iter->stringval);
    current_field->datatype = iter->symtype;
    current_field->size = iter->symtype->size;
    current_field->offset = offset;

    offset += current_field->size;
    if(iter->link && (iter->link->symtype->size + offset) % 8 != 0) {
      offset = wordaddress(offset, 8);
    }

    if(is_first) {
      is_first = 0;

      prev_field->datatype = current_field;
      prev_field = prev_field->datatype;
    } else {
      prev_field->link = current_field;
      prev_field = prev_field->link;
    }

    iter = iter->link;
  }

  recsym->size = offset;
  
  return rectok;
}


/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok) {
  TOKEN iter = idlist;
  do {
    iter->symtype = typetok->symtype;
    iter = iter->link;
  } while(iter);

  return idlist;
}


/* instdotdot installs a .. subrange in the symbol table.
   dottok is a (now) unused token that is recycled. */
TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  memset(dottok, 0, sizeof(*dottok));
  return makesubrange(dottok, lowtok->intval, hightok->intval);
}


/* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist) {
  TOKEN iter = idlist;
  int num_const = 0;
  TOKEN consttok = NULL;
  SYMBOL sym_int = searchst("integer");

  while(iter != NULL) {
    // make a const token
    consttok = (TOKEN)talloc();
    consttok->tokentype = NUMBERTOK;
    consttok->basicdt = INTEGER;
    consttok->symtype = sym_int;
    consttok->intval = num_const;

    instconst(iter, consttok);
    
    num_const++;
    consttok = NULL;
    iter = iter->link;
  }

  return makesubrange((TOKEN)talloc(), 0, num_const - 1);
}

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high) {
  SYMBOL symentry = makesym("SUBRANGE");

  symentry->kind = SUBRANGE;
  symentry->basicdt = INTEGER;
  symentry->datatype = searchst("integer");
  symentry->size = symentry->datatype->size;
  symentry->lowbound = low;
  symentry->highbound = high;
  
  tok->symtype = symentry;
  tok->symentry = symentry;
  return tok;
}


TOKEN reverse_tok_list_recur(TOKEN prev, TOKEN list, TOKEN* new_first){ 
  if(list == NULL) {
    *new_first = prev;
  } else {
    TOKEN new_prev = reverse_tok_list_recur(list, list->link, new_first);
    new_prev->link = prev;
  }
  return prev;
}

TOKEN reverse_tok_list(TOKEN list){ 
  if(list->link == NULL) {
    return list;
  }
  TOKEN new_first = NULL;

  reverse_tok_list_recur(list, list->link, &new_first);
  list->link = NULL;
  return new_first;
}

/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok) {
  TOKEN reversed_bounds = reverse_tok_list(bounds);
  TOKEN bound_iter = reversed_bounds;

  SYMBOL before_arysym = NULL;
  SYMBOL arysym = NULL;

  while(bound_iter != NULL) {
    SYMBOL bound_sym = bound_iter->symtype;

    while(bound_sym->kind != SUBRANGE) {
      bound_sym = bound_sym->datatype;
    }

    arysym = makesym(" ");
    arysym->kind = ARRAYSYM;
    /* arysym->datatype = bound_sym; */
    arysym->datatype = before_arysym == NULL ? typetok->symtype : bound_sym;
    arysym->lowbound = bound_sym->lowbound;
    arysym->highbound = bound_sym->highbound;
    arysym->size = arysym->datatype->size * 
                      (arysym->highbound - arysym->lowbound + 1);
    
    if(before_arysym) {
      arysym->size *= before_arysym->highbound - before_arysym->lowbound + 1;
      arysym->datatype = before_arysym;
    }

    bound_iter = bound_iter->link;
    before_arysym = arysym;
  }

  memset(typetok, 0, sizeof(*typetok));

  typetok->tokentype = RESERVED;
  typetok->symtype = arysym;
  typetok->whichval = ARRAY - RESERVED_BIAS;

  return typetok;
}

/* dopoint handles a ^ operator.  john^ becomes (^ john) with type record
   tok is a (now) unused token that is recycled. */
TOKEN dopoint(TOKEN var, TOKEN tok) {
  tok->operands = var;

  //TODO
  SYMBOL iter = NULL;
  if (var->tokentype == IDENTIFIERTOK) {
    iter = searchst(var->stringval);
  } else {
    iter = var->symtype;
  }

  while(iter->kind != POINTERSYM) {
    iter = iter->datatype;
  }
  tok->symtype = iter->datatype;
  return tok;
}


int find_offset(SYMBOL first_field,
                char* dst_field_name,
                int* offset,
                SYMBOL* dst_field_type) {

  SYMBOL iter_field = first_field;

  while(iter_field != NULL) {
    if(iter_field->datatype->datatype &&
       iter_field->datatype->datatype->kind == RECORDSYM) {

      /* call function recursively */
      int is_field_found = find_offset(
                                iter_field->datatype->datatype->datatype,
                                dst_field_name,
                                offset,
                                dst_field_type);
      
      if(is_field_found == 1) {
        *dst_field_type = iter_field->datatype;
        *offset += iter_field->offset;
        return 1;
      }
    }

    /*if dst field is found! */
    if(strcmp(iter_field->namestring, dst_field_name) == 0) {
      *dst_field_type = iter_field->datatype;
      *offset += iter_field->offset;
      return 1;
    }

    iter_field = iter_field->link;
  }

  return 0;
}

// iterate whole list and find 
TOKEN optimize_aref(TOKEN list) {
  if (list == NULL) {
    return NULL;
  }

  if (list->operands) {
    TOKEN next = list->operands;
    if ( (list->tokentype == OPERATOR && list->whichval == AREFOP)
          && (next->tokentype == OPERATOR && next->whichval == AREFOP) ) {
      // Optimize!!

      // sum offsets
      TOKEN num_tok = next->operands->link;

      while(num_tok->tokentype != NUMBERTOK) {
        // When the index is not a constant.
        num_tok = num_tok->operands;
      }

      num_tok->intval += next->link->intval;
      free(next->link);
      next->link = list->link;


      // change list to next
      next->symtype = list->symtype;
      next->symentry = list->symentry;
      free(list);
      list = next;

      // iterate
      list = optimize_aref(list);
    } else{
      // iterate
      list->operands = optimize_aref(list->operands);
    }
  }

  if (list->link) {
    // iterate
    list->link = optimize_aref(list->link);
  }

  return list;
}

/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  TOKEN aref = dot;

  memset(aref, 0, sizeof(*aref));
  aref->tokentype = OPERATOR;
  aref->whichval = AREFOP;
  aref->operands = var;
  /* aref->symtype = var->symtype; */

  if( ! var->symtype ) {
    SYMBOL iter = searchst(var->stringval);
    while(iter->kind != TYPESYM) {
      iter = iter->datatype;
    }

    var->symtype = iter;
  }

  SYMBOL rec_sym = var->symtype;
  while(rec_sym->kind != RECORDSYM) {
    rec_sym = rec_sym->datatype;
  }
  SYMBOL iter_field = rec_sym->datatype;

  int sub_offset = 0;
  SYMBOL sub_field_type = NULL;
  int is_sub_field_found = 0;

  /* if there is no field, seg fault occurs */
  while(strcmp(iter_field->namestring, field->stringval) != 0) {
    if(iter_field->datatype->datatype &&
       iter_field->datatype->datatype->kind == RECORDSYM) {
       is_sub_field_found = find_offset(
                            iter_field->datatype->datatype->datatype,
                            field->stringval,
                            &sub_offset,
                            &sub_field_type
                            );

       if(is_sub_field_found) {
         break;
       }
     }
    iter_field = iter_field->link;
  }

  TOKEN offset_tok = (TOKEN)talloc();
  offset_tok->tokentype = NUMBERTOK;
  /* offset_tok->intval = iter_field->offset + sub_offset; */
  offset_tok->intval = is_sub_field_found ? sub_offset : iter_field->offset;
  aref->symtype = is_sub_field_found ? sub_field_type : iter_field->datatype;

  var->link = offset_tok;

  return optimize_aref(aref);
}


/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN number, TOKEN statement) {
  TOKEN progntok = (TOKEN)talloc();

  progntok->tokentype = OPERATOR;
  progntok->whichval = PROGNOP;

  memset(labeltok, 0, sizeof(*labeltok));
  labeltok->tokentype = OPERATOR;
  labeltok->whichval = LABELOP;

  progntok->operands = labeltok;

  int num_inner_label;
  for ( num_inner_label = 0;
        num_inner_label < MAX_LABEL;
        num_inner_label++ ) {
    if (labels[num_inner_label] == number->intval) {
      break;
    }
  }

  if (num_inner_label >= MAX_LABEL) {
    // Cannot find label
    *((int*)0) = 0;
  }

  TOKEN num_label_tok = (TOKEN)talloc();
  num_label_tok->tokentype = NUMBERTOK;
  num_label_tok->basicdt = INTEGER;
  num_label_tok->symtype = searchst("integer");
  num_label_tok->intval = num_inner_label;

  labeltok->operands = num_label_tok;
  labeltok->link = statement;


  return progntok;
}


TOKEN nil_to_zero(TOKEN nil) {
  memset(nil, 0, sizeof(*nil));

  nil->tokentype = NUMBERTOK;
  nil->basicdt = INTEGER;
  nil->intval = 0;

  return nil;
}

/* arrayref processes an array reference a[i]
   subs is a list of subscript expressions.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN arrayref(TOKEN arr, TOKEN aref, TOKEN subs, TOKEN tokb) {
  arr->symtype = searchst(arr->stringval);
  SYMBOL subrange = arr->symtype->datatype;

  free(aref);
  aref = NULL;

  TOKEN next_aref = arr;

  TOKEN iter_subs = subs;
  SYMBOL type_iter = subrange;

  while(iter_subs != NULL) {
    aref = (TOKEN)talloc();
    aref->tokentype = OPERATOR;
    aref->whichval = AREFOP;
    aref->operands = next_aref;
    aref->symtype = next_aref->symtype;

    int unit_size = type_iter->datatype->size;

    if (iter_subs->tokentype == NUMBERTOK) {
      // Just add number.
      TOKEN tok_number = (TOKEN)talloc();
      tok_number->tokentype = NUMBERTOK;
      tok_number->basicdt = INTEGER;
      tok_number->intval = (iter_subs->intval - type_iter->lowbound) 
                             * unit_size;

      aref->operands->link = tok_number;
    } else {
      // Operations for variable index.
      TOKEN plus_tok = (TOKEN)talloc();
      plus_tok->tokentype = OPERATOR;
      plus_tok->whichval = PLUSOP;
      aref->operands->link = plus_tok;

      TOKEN num_neg_tok = (TOKEN)talloc();
      num_neg_tok->tokentype = NUMBERTOK;
      num_neg_tok->basicdt = INTEGER;
      num_neg_tok->intval = -unit_size;

      plus_tok->operands = num_neg_tok;

      TOKEN times_op_tok = (TOKEN)talloc();
      times_op_tok->tokentype = OPERATOR;
      times_op_tok->whichval = TIMESOP;
      num_neg_tok->link = times_op_tok;

      TOKEN num_pos_tok = (TOKEN)talloc();
      num_pos_tok->tokentype = NUMBERTOK;
      num_pos_tok->basicdt = INTEGER;
      num_pos_tok->intval = unit_size;
      times_op_tok->operands = num_pos_tok;

      TOKEN var_idx = (TOKEN)talloc();
      memcpy(var_idx, iter_subs, sizeof(*var_idx));
      var_idx->link = NULL;

      num_pos_tok->link = var_idx;
    }
    
    iter_subs = iter_subs->link;
    type_iter = type_iter->datatype;
    next_aref = aref;
  }


  return optimize_aref(aref);
  /* return aref; */
}

/* arrayref processes an array reference a[i]
   subs is a list of subscript expressions.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN arrayref_old(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
  arr->symtype = searchst(arr->stringval);
  SYMBOL subrange = arr->symtype->datatype;

  int unit_size = subrange->datatype->size;

  memset(tok, 0, sizeof(*tok));
  tok->tokentype = OPERATOR;
  tok->whichval = AREFOP;
  tok->operands = arr;
  tok->symtype = arr->symtype;

  TOKEN iter_subs = subs;
  TOKEN oper_iter = tok;

  while(iter_subs != NULL) {
    TOKEN new_tok = (TOKEN)talloc();

    if(iter_subs->tokentype == NUMBERTOK) {
      // index is a constant
      new_tok->tokentype = NUMBERTOK;
      new_tok->basicdt = INTEGER;
      new_tok->intval = (iter_subs->intval - subrange->lowbound) * unit_size;

      oper_iter->operands->link = new_tok;
    } else {
      new_tok->tokentype = OPERATOR;
      new_tok->whichval = PLUSOP;
      oper_iter->operands->link = new_tok;

      TOKEN num_minus_tok = (TOKEN)talloc();
      num_minus_tok->tokentype = NUMBERTOK;
      num_minus_tok->basicdt = INTEGER;
      num_minus_tok->intval = -unit_size;

      new_tok->operands = num_minus_tok;

      TOKEN times_op_tok = (TOKEN)talloc();
      times_op_tok->tokentype = OPERATOR;
      times_op_tok->whichval = TIMESOP;
      num_minus_tok->link = times_op_tok;

      TOKEN num_plus_tok = (TOKEN)talloc();
      num_plus_tok->tokentype = NUMBERTOK;
      num_plus_tok->basicdt = INTEGER;
      num_plus_tok->intval = unit_size;
      times_op_tok->operands = num_plus_tok;

      num_plus_tok->link = iter_subs;
    }
    iter_subs = iter_subs->link;
  }
  return tok;
}

/*
while c do s
(PROGN (LABEL j)
       (IF c (PROGN s (GOTO j))))
*/

/* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN progn1, TOKEN expr, TOKEN progn2, TOKEN statement) {
  memset(progn1, 0, sizeof(*progn1));
  progn1->tokentype = OPERATOR;
  progn1->whichval = PROGNOP;
  memcpy(progn2, progn1, sizeof(*progn2));

  TOKEN label = makelabel();
  progn1->operands = label;

  TOKEN if_tok = (TOKEN)talloc();
  if_tok->tokentype = OPERATOR;
  if_tok->whichval = IFOP;

  label->link = if_tok;
  if_tok->operands = expr;

  expr->link = progn2;
  progn2->operands = statement;

  TOKEN goto_tok = (TOKEN)talloc();
  goto_tok->tokentype = OPERATOR;
  goto_tok->whichval = GOTOOP;

  TOKEN num_label = (TOKEN)talloc();
  memcpy(num_label, label->operands, sizeof(*num_label));

  goto_tok->operands = num_label;

  statement->link = goto_tok;

  TOKEN opt_return = optimize_progn(progn2);
  if (opt_return) {
    expr->link = opt_return;
  }

  return progn1;
}

/* dogoto is the action for a goto statement.
   tok is a (now) unused token that is recycled. */
TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
  memset(tok, 0, sizeof(*tok));
  tok->tokentype = OPERATOR;
  tok->whichval = GOTOOP;

  int num_inner_label;
  for ( num_inner_label = 0;
        num_inner_label < MAX_LABEL;
        num_inner_label++ ) {
    if (labels[num_inner_label] == labeltok->intval) {
      break;
    }
  }

  TOKEN inner_label_tok = (TOKEN)talloc();
  inner_label_tok->tokentype = NUMBERTOK;
  inner_label_tok->basicdt = INTEGER;
  inner_label_tok->intval = num_inner_label;

  tok->operands = inner_label_tok;

  return tok;
}


int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}


int main(void)          /*  */
  { int res;
    initsyms();
    res = yyparse();
    /* printst();       [> to shorten, change to:  printstlevel(1);  <] */
    printstlevel(1);       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
  }
