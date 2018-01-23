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

/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
   */

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
  int cc;

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


      printf("skip blank or whitespace\n");


    } else {
      // comments cases

      /** Comment type 1 : { comment } */
      if (skiptype == SKIP_COMMENT_TYPE_1) {
        do {
          getchar();
          c = peekchar();



          printf("skip comment 1\n");



        } while ( c != EOF && c != '}');
        getchar();

      /** Comment type 2 : (* comment *) */
      } else if (skiptype == SKIP_COMMENT_TYPE_2) {
        do {
          getchar();

          c = peekchar();
          cc = peek2char();


          printf("skip comment 2\n");


        } while (
            c != EOF && cc != EOF
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

/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok) {
}

TOKEN getstring (TOKEN tok) {
}

TOKEN special (TOKEN tok) {
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

