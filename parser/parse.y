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

int sign_of_for(TOKEN from_expr, TOKEN to_expr);
void instvars(TOKEN idlist, TOKEN typetok);

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

program    :  PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON vblock DOT
                { $1->tokentype = OPERATOR;
                  $1->whichval = PROGRAMOP;
                  $1->operands = makeprogram($2, makeprogn($3, $4), $7);
                  parseresult = $1; }
             ;

  id_list    :  IDENTIFIER COMMA id_list       { $$ = cons($1, $3); }
             |  IDENTIFIER                     { $$ = cons($1, NULL); }
             ; 

  vdef       :  VAR id_list COLON type SEMICOLON { instvars($2, $4); }
             ;

  type       :  simple_type
             ;

  simple_type:  IDENTIFIER                     { $$ = findtype($1); }
             ;

  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             |  assignment
             |  FOR IDENTIFIER ASSIGN expr TO expr DO statement
                      {
                        if (DEBUG) {
                          printf("before entering makefor()\n");
                          dbugprinttok($1);
                          dbugprinttok($2);
                          dbugprinttok($3);
                          dbugprinttok($4);
                          dbugprinttok($5);
                          dbugprinttok($6);
                          dbugprinttok($7);
                          dbugprinttok($8);
                        }
                        
                        $$ = makefor(sign_of_for($4, $6), $1,
                                        binop($3, $2, $4), $5, $6, $7, $8);
                        $$ = makeprogn($1, $$); 
                      }
             |  funcall
             ;

  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
  assignment :  IDENTIFIER ASSIGN expr         { $$ = binop($2, $1, $3); }
             ;
  expr       :  expr PLUS term                 { $$ = binop($2, $1, $3); }
             |  term 
             ;
  term       :  term TIMES factor              { $$ = binop($2, $1, $3); }
             |  factor
             ;
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  IDENTIFIER
             |  NUMBER
             |  funcall
             ;
  funcall    :  IDENTIFIER LPAREN STRING RPAREN 
                                              { $$ = makefuncall($2, $1, $3); }
             ;

  vblock     :  vdef block                     { $$ = $2; }
             |  block
             ;

  block      :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
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
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
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

TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  tok->tokentype = OPERATOR;
  tok->whichval = FUNCALLOP;
  tok->operands = fn;
  fn->link = args;

  if (DEBUG) {
    printf("makefuncall\n");
    dbugprinttok(tok);
    dbugprinttok(fn);
    dbugprinttok(args);
  }

  return tok;
}

int sign_of_for(TOKEN from_expr, TOKEN to_expr) {
  int from, to;
  SYMBOL to_symbol = NULL;
  from = from_expr->intval;
  sscanf(to_expr->stringval, "%d", &to);
  //TODO: fix it.

  to_symbol = searchst(to_expr->stringval);


  if (DEBUG) {
    printf("sign_of_for\n");
    dbugprinttok(from_expr);
    dbugprinttok(to_expr);
  }

  return from < to ? 1 : -1; 
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
  TOKEN le_token = tokc;
  le_token->tokentype = OPERATOR;
  le_token->whichval = LEOP;

  if_token->operands = le_token; 

  le_token->operands = (TOKEN)talloc();
  memcpy(le_token->operands, asg->operands, sizeof(*le_token->operands));
  le_token->operands->link = endexpr;

  le_token->link = makeprogn(talloc(), statement);


  TOKEN count_assign = (TOKEN)talloc();
  count_assign->tokentype = OPERATOR;
  count_assign->whichval = ASSIGNOP;

// after funcall
  count_assign->operands = (TOKEN)talloc();
  memcpy(count_assign->operands, le_token->operands,
    sizeof(*count_assign->operands));
  
  TOKEN left_i = count_assign->operands;
  TOKEN inc = (TOKEN)talloc();

  left_i->link = inc;
  inc->tokentype = OPERATOR;
  inc->whichval = PLUSOP; 

  TOKEN second_left_i = (TOKEN)talloc();
  memcpy(second_left_i, le_token->operands, sizeof(*second_left_i));

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
    printst();       /* to shorten, change to:  printstlevel(1); */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }
