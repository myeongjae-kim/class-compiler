/* lexanc.c      22 Jan 18  */

/* Myeongjae Kim */



/* lex1.c         14 Feb 01; 31 May 12; 11 Jan 18       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2018 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.
   */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"

#define true 1
#define false 0
#define bool int

#include "assert.h"
#define MAX_CHAR 16

/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
   */


extern int CHARCLASS[MAXCHARCLASS];


/** char* operators[]  = {" ", "+", "-", "*", "/", ":=", "=", "<>", "<", "<=",
  *                           ">=", ">",  "^", ".", "and", "or", "not", "div",
  *                           "mod", "in", "if", "goto", "progn", "label",
  *                           "funcall", "aref", "program", "float"}; */

char* operators[]  = {" ", "+", "-", "*", "/", ":=", "=", "<>", "<", "<=",
                          ">=", ">",  "^", ".", "and", "or", "not", "div",
                          "mod", "in"};
const int max_operators = sizeof(operators) / sizeof(char*);
/* 28, [27] is "float" */

char *delimiters[] = { "  ", " ,", " ;", " :", " (", " )", " [", " ]",
                           ".."} ;
const int max_delimiters = sizeof(delimiters) / sizeof(char*);
/* 9, [8] is ".." */

char *reserveds[] = { " ", "array", "begin", "case", "const", "do",
                           "downto", "else", "end", "file", "for",
		           "function", "goto", "if", "label", "nil",
                           "of", "packed", "procedure", "program", "record",
                           "repeat", "set", "then", "to", "type",
		           "until", "var", "while", "with" };
/* 30, [29] is "with" */
const int max_reserveds = sizeof(reserveds) / sizeof(char*);

enum skip_t {SKIP_INVALID, SKIP_BLANK, SKIP_WHITESPACE,
  SKIP_COMMENT_TYPE_1,
  SKIP_COMMENT_TYPE_2,
  SKIP_COMMENT_TYPE_3,
};

bool is_blank(enum skip_t* skiptype) {
  int c;
  if ((c = peekchar()) != EOF
      && (c == ' ')) {

    *skiptype = SKIP_BLANK;
    return true;
  }
  return false;
}

bool is_whitespace(enum skip_t* skiptype) {
  int c;
  if ((c = peekchar()) != EOF
      && (c == '\n' || c == '\t')) {

    *skiptype = SKIP_WHITESPACE;
    return true;
  }
  return false;
}

bool is_comments(enum skip_t* skiptype) {
  int c;

  /** Comment type 1 : { comment } */
  if ((c = peekchar()) != EOF
      && (c == '{')) {

    *skiptype = SKIP_COMMENT_TYPE_1;
    return true;
  }

  /** Comment type 2 : (* comment *) */
  if ((c = peekchar()) != EOF
      && (c == '(')
      && (c = peek2char()) != EOF
      && (c == '*')
      ) {

    *skiptype = SKIP_COMMENT_TYPE_2;
    return true;
  }

  return false;
}

bool is_blank_or_whitespace(char c) {
  if (c == ' ' || c == '\n' || c != '\t') {
    return true;
  } else {
    return false;
  }
}

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks () {
  int c;
  int cc;

  /* if next character is blanks, whitespace, or comments,
   * remove them */

  enum skip_t skiptype = SKIP_INVALID;
  while (is_blank(&skiptype)
      || is_whitespace(&skiptype)
      || is_comments(&skiptype)) {

    assert(skiptype != SKIP_INVALID);
    if (skiptype == SKIP_BLANK ||
        skiptype == SKIP_WHITESPACE) {
      // remove one char
      getchar();
    } else {
      // comments cases

      /** Comment type 1 : { comment } */
      if (skiptype == SKIP_COMMENT_TYPE_1) {
        do {
          getchar();
          c = peekchar();
        } while ( c != EOF && c != '}');
        getchar();

      /** Comment type 2 : (* comment *) */
      } else if (skiptype == SKIP_COMMENT_TYPE_2) {
        do {
          getchar();

          c = peekchar();
          cc = peek2char();
        } while ( c != EOF && cc != EOF
            && !(c == '*' && cc == ')') );
        getchar();
        getchar();
      } else {
        // Invalid cases
        perror("Invalid comment case");
        assert(false);
        *((int*)0) = 0;
      }
    }
    /** reinitialize */
    skiptype = SKIP_INVALID;
  }

  /* skip blanks and whitespace. */
  /** while ((c = peekchar()) != EOF
   *     && (c == ' ' || c == '\n' || c == '\t')) {
   *   getchar();
   * } */
}

/* Get identifiers and reserved words, or operator words */
TOKEN identifier (TOKEN tok) {
  /* check whether it is reserved word first */
  /* It is guaranteed that first char is alphabet */
  int nc, i;
  char c;

  /* get the string */
  memset(tok->stringval, 0, sizeof(tok->stringval));
  for (nc = 0; nc < MAX_CHAR - 1; ++nc) {
    c = peekchar();
    if (CHARCLASS[(int)c] == ALPHA || CHARCLASS[(int)c] == NUMERIC) {
      getchar();
      tok->stringval[nc] = c;
    } else {
      break;
    }
  }

  /* truncate string whose size is bigger than MAX_CHAR - 1 */
  if (nc == MAX_CHAR - 1) {
    while ((c = peekchar()) != EOF
        && (! is_blank_or_whitespace(c)) ) {
      getchar();
    }
  }

  /* check whether it is a reserved word */
  bool is_tokentype_found = false;
  for (i = 1; i < max_reserveds && is_tokentype_found == false; ++i) {
    if (strcmp(tok->stringval, reserveds[i]) == 0) {
      tok->tokentype = RESERVED;

      // reset string and get the number of token
      memset(tok->stringval, 0, sizeof(tok->stringval));
      tok->whichval = i;
      is_tokentype_found = true;
    }
  }

  /* check whether it is an operator */
  /* 14 is the number of the first string operator */
  for (i = 14; i < max_operators && is_tokentype_found == false; ++i) {
    if (strcmp(tok->stringval, operators[i]) == 0) {
      tok->tokentype = OPERATOR;

      // reset string and get the number of token
      memset(tok->stringval, 0, sizeof(tok->stringval));
      tok->whichval = i;
      is_tokentype_found = true;
    }
  }

  
  /* otherwise, identifier */
  if ( ! is_tokentype_found) {
    tok->tokentype = IDENTIFIERTOK;
  }
  return tok;
}

TOKEN getstring (TOKEN tok) {
  int nc;
  int c, cc;
  bool str_end_met = false;

  /* the first character is '\''. Remove it */
  getchar();

  /* get the string */
  memset(tok->stringval, 0, sizeof(tok->stringval));
  for (nc = 0; nc < MAX_CHAR - 1; ++nc) {
    c = peekchar();
    if (c != '\'') {
      getchar();
      tok->stringval[nc] = c;
    } else if (peek2char() == '\''){
      getchar();
      getchar();
      tok->stringval[nc] = c;
    } else {
      /* when it meets '\'' only, not '\'\'' */
      str_end_met = true;
      break;
    }
  }

  while ( ! str_end_met) {
    /* truncate string whose size is bigger than MAX_CHAR - 1 */
    c = peekchar();
    cc = peek2char();
    if ( !(c == '\'' && cc == '\'')) {
      str_end_met = true;
      getchar();
      getchar();
    } else if (c == '\n' || c == EOF) {
      perror("String is not closed. Appostrophe is omitted");
      *((int*)0) = 0;
    } else {
      /* more string. continue while loop */
      getchar();
    }
  }

  tok->tokentype = STRINGTOK;
  return tok;
}

/* operator or delimiter */
TOKEN special (TOKEN tok) {
  /* string operators were checked in identifier() */
  int i, nc;
  char c;

  /* get special characters */
  memset(tok->stringval, 0, sizeof(tok->stringval));
  for (nc = 0; nc < MAX_CHAR - 1; ++nc) {
    c = peekchar();
    if (CHARCLASS[(int)c] == SPECIAL) {
      tok->stringval[nc] = c;
      getchar();
    } else {
      break;
    }
  }

  if (nc == MAX_CHAR - 1) {
    perror("There is no special characters that long");
    assert(false);
    *((int*)0) = 0;
  }

  /* check whether it is an operator */
  bool is_tokentype_found = false;
  for (i = 1; i < max_operators && is_tokentype_found == false; ++i) {
    if (strcmp(tok->stringval, operators[i]) == 0) {
      tok->tokentype = OPERATOR;

      // reset string and get the number of token
      memset(tok->stringval, 0, sizeof(tok->stringval));
      tok->whichval = i;
      is_tokentype_found = true;
    }
  }


  /* check whether it is a delimiter */
  for (i = 1; i < max_delimiters && is_tokentype_found == false; ++i) {
    if (strcmp(tok->stringval, delimiters[i]) == 0) {
      tok->tokentype = DELIMITER;

      // reset string and get the number of token
      memset(tok->stringval, 0, sizeof(tok->stringval));
      tok->whichval = i;
      is_tokentype_found = true;
    }
  }

  /* if it is not an operaor or a delimiter, its error */
  if (is_tokentype_found == false) {
    perror("No matching token type");
    *((int*)0) = 0;
  }

  return tok;
}

/* Get and convert unsigned numbers of all types. */
TOKEN number (TOKEN tok) {
  long num;
  int  c, charval;
  num = 0;
  while ( (c = peekchar()) != EOF
      && CHARCLASS[c] == NUMERIC) {
    c = getchar();
    charval = (c - '0');
    num = num * 10 + charval;
  }

  tok->tokentype = NUMBERTOK;
  tok->basicdt = INTEGER;
  tok->intval = num;
  return (tok);
}

