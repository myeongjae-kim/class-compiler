/* TODO: if-else ambiguity, and other grammars */
/* TODO: Now get rid of label 1492: after john^.age := 19 */


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
             |  IF expression THEN statement
             |  variable ASSIGN expression { $$ = binop($2, $1, $3); }
             |  funcall
             |  WHILE expression DO statement
             |  REPEAT statement_list UNTIL expression
                                         { $$ = makerepeat($1, $2, $3, $4);
                                           $$ = makeprogn($1, $$);
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
             |  GOTO NUMBER
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
  unsigned_constant :  IDENTIFIER {check_const($1);}| NUMBER | NIL | STRING
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
             |  POINT IDENTIFIER            { $$ = instpoint($1, $2); /*TODO*/}
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
  
  lblock     :  LABEL numlist SEMICOLON cblock 
                                            { instlabel($2); $$ = $4; }
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
  tdef       :  IDENTIFIER EQ type           { insttype($1, $3); /*TODO*/}
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
                                  { $$ = makeprogn($1,cons($2, $3)); }
             ;
  label      :  NUMBER COLON statement  
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
    } else if (!lhs_sym && lhs->basicdt == REAL) {
      op->symtype = real_sym;
    } else if (lhs_sym 
                && lhs_sym == int_sym || lhs_sym->datatype == int_sym) {
      op->symtype = int_sym;
    } else if (lhs_sym 
                && lhs_sym == real_sym || lhs_sym->datatype == real_sym) {
      op->symtype = real_sym;
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

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

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

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = real_sym;
          } else if((lhs_sym == real_sym || lhs_sym->datatype == real_sym)
            && (rhs_sym == int_sym || rhs_sym->datatype == int_sym)) {
            // need to coerce
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;

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

          // rhs is not a constant
          } else if (rhs_sym == real_sym
                      || (rhs_sym && rhs_sym->datatype == real_sym)) {
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FIXOP;
            coerce_tok->symtype = int_sym;

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = int_sym;
          }

        // left is real and right is integer
        } else if (lhs_sym == real_sym || lhs_sym->datatype == real_sym){

          // rhs is constant
          if(!rhs_sym && rhs->basicdt == INTEGER) {
            rhs->basicdt = REAL;
            rhs->realval = rhs->intval;
            op->symtype = real_sym;

          // rhs is not a constant
          } else if (rhs_sym == int_sym
                      || (rhs_sym && rhs_sym->datatype == int_sym)) {
            coerce_tok = (TOKEN)talloc();
            coerce_tok->tokentype = OPERATOR;
            coerce_tok->whichval = FLOATOP;
            coerce_tok->symtype = real_sym;

            coerce_tok->operands = rhs;
            lhs->link = coerce_tok;

            op->symtype = real_sym;
          }
        }


        break;
      
      case EQOP:
      case LTOP:
      case GTOP:
      case NEOP:
      case LEOP:
      case GEOP:
      case INOP:
        if (DEBUG) printf("\t\t\tcompare op\n");
        // TODO
        break;
      

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
  static int labels[1024];
  do {
    labels[labelnumber++] = tok->intval;
    tok = tok->link;
  } while (tok);
}


/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL typesym = searchins(typename->stringval);
  typesym->kind = TYPESYM;
  typesym->datatype = typetok->symtype;
  typesym->size = typesym->datatype->size;
}


/* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL pointsym = makesym(" ");
  pointsym->kind = POINTERSYM;

  pointsym->datatype = searchins(typename->stringval);
  pointsym->size = alignsize(pointsym);

  tok->symtype = pointsym;
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
  SYMBOL iter = searchst(var->stringval);
  while(iter->kind != POINTERSYM) {
    iter = iter->datatype;
  }
  tok->symtype = iter->datatype;
  return tok;
}


/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  TOKEN aref = dot;

  memset(aref, 0, sizeof(*aref));
  aref->tokentype = OPERATOR;
  aref->whichval = AREFOP;
  aref->operands = var;
  aref->symtype = var->symtype;

  SYMBOL rec_sym = var->symtype;
  SYMBOL iter_field = rec_sym->datatype->datatype;

  while(strcmp(iter_field->namestring, field->stringval) != 0) {
    iter_field = iter_field->link;
  }

  TOKEN offset_tok = (TOKEN)talloc();
  offset_tok->tokentype = NUMBERTOK;
  offset_tok->intval = iter_field->offset;

  var->link = offset_tok;

  return aref;
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
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }
