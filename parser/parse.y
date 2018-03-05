/* TODO: if-else ambiguity, and other grammars */


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
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

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
             |  variable ASSIGN expression
             |  funcall
             |  WHILE expression DO statement
             |  REPEAT statement_list UNTIL expression
             |  FOR IDENTIFIER ASSIGN expression TO expression DO statement
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
  unsigned_constant :  IDENTIFIER | NUMBER | NIL | STRING
                    ;
  sign       :  PLUS
             |  MINUS
             ;
  constant   :  sign IDENTIFIER
             |  IDENTIFIER
             |  sign NUMBER
             |  NUMBER
             |  STRING
             ;
  id_list    :  IDENTIFIER COMMA id_list       { $$ = cons($1, $3); }
             |  IDENTIFIER                     { $$ = cons($1, NULL); }
             ; 
  simple_type:  IDENTIFIER
             |  LPAREN id_list RPAREN          { $$ = $2; }
             |  constant DOTDOT constant
             ;
  simple_type_list : simple_type COMMA simple_type_list { $$ = cons($1, $3); }
                   | simple_type                        {$$ = cons($1, NULL);}
                   ;
  fields     :  id_list COLON type
             ;
  field_list :  fields SEMICOLON field_list { $$ = cons($1, $3); }
             |  fields                      { $$ = cons($1, NULL); }
             ;
  type       :  simple_type
             |  ARRAY LBRACKET simple_type_list RBRACKET OF type
             |  RECORD field_list END       { $$ = $2; }
             |  POINT IDENTIFIER
             ;
  plus_op    :  PLUS | MINUS | OR
             ;
  simple_expression : sign term             { $$ = $2; }
                    | term
                    | simple_expression plus_op term
                    ;
  compare_op :  EQ | LT | GT | NE | LE | GE | IN
             ;
  expression :  expression compare_op simple_expression
             |  simple_expression
             ;
  expr_list  :  expression COMMA expr_list  { $$ = cons($1, $3); }
             |  expression
             ;
  variable   :  IDENTIFIER
             |  variable LBRACKET expr_list RBRACKET
             |  variable DOT IDENTIFIER
             |  variable POINT
             ;
  funcall    :  IDENTIFIER LPAREN STRING RPAREN 
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
             |  cblock
             ;
  cblock     :  CONST cdef_list tblock
             |  tblock
             ;
  cdef       :  IDENTIFIER EQ constant
             ;
  cdef_list  :  cdef SEMICOLON cdef_list
             |  /* empty */       { $$ = NULL; } /* TODO: right? */
             ;
  tblock     :  TYPE tdef_list vblock
             |  vblock
             ;
  tdef       :  IDENTIFIER EQ type
             ;
  tdef_list  :  tdef SEMICOLON tdef_list
             |  /* empty */       { $$ = NULL; } /* TODO: right? */
             ;
  vblock     :  VAR vdef_list block
             |  block
             ;
  vdef       :  id_list COLON type
             ;
  vdef_list  :  vdef SEMICOLON vdef_list
             |  /* empty */       { $$ = NULL; } /* TODO: right? */
             ;
  block      :  BEGINBEGIN statement endpart
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
    printst();       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }
