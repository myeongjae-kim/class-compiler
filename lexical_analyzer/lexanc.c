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

#include <assert.h>
#include <limits.h>
#include <float.h>
#define MAX_CHAR 16
#define NUM_BUFF_MAX 1026

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

char *delimiters[] = { " ", ",", ";", ":", "(", ")", "[", "]", ".."} ;
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
  if (c == ' ' || c == '\n' || c == '\t') {
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
        getchar();
        /* go ahead with only one character */
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
        fprintf(stderr, "Invalid comment case\n");
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
      getchar();
      str_end_met = true;
      break;
    }
  }

  while ( ! str_end_met) {
    /* truncate string whose size is bigger than MAX_CHAR - 1 */
    c = peekchar();
    cc = peek2char();
    if (c == '\'' && cc != '\'') {
      str_end_met = true;
      getchar();
    } else if (c == '\n' || c == EOF) {
      fprintf(stderr, "String is not closed. Appostrophe is omitted.\n");
      *((int*)0) = 0;
    } else {
      /* more string. continue while loop */
      getchar();
    }
  }

  tok->tokentype = STRINGTOK;
  tok->basicdt = STRINGTYPE;
  return tok;
}

/* operator or delimiter */
TOKEN special (TOKEN tok) {
  /* string operators were checked in identifier() */
  int i, nc;
  char c, cc;
  bool is_tokentype_found = false;

  /* get special characters */
  /* only two characters */

  c = peekchar();
  cc = peek2char();

  memset(tok->stringval, 0, sizeof(tok->stringval));
  nc = 0;
  tok->stringval[nc++] = c;
  tok->stringval[nc++] = cc;

  /* nc is 2 */
  for (; nc > 0; --nc) {
    /* check whether it is an operator */
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

    if (is_tokentype_found == true) {
      if (nc == 2) {
        // two char operator
        getchar();
        getchar();
      } else if (nc == 1) {
        // one char operator or delimiter
        getchar();
      } else {
        // impossible case
        assert(false);
      }
      break;
    } else {
      /* make string size 1 */
      tok->stringval[1] = '\0';
    }
  }

  /* if it is not an operaor or a delimiter, its error */
  if (is_tokentype_found == false) {
    fprintf(stderr, "No matching token type of the character: %c\n", c);
    *((int*)0) = 0;
  }

  return tok;
}


long get_integer_from_input(bool* is_int_overflowed) {
  char c, charval;
  long int_num = 0;
  while ( (c = peekchar()) != EOF
      && CHARCLASS[(int)c] == NUMERIC) {
    c = getchar();
    charval = (c - '0');
    int_num = int_num * 10 + charval;

    if (is_int_overflowed != NULL && int_num > INT_MAX) {
      *is_int_overflowed = true;
    }
  }

  return int_num;
}

long get_nine_digit_integer() {
  char c, charval;
  long int_num = 0;
  int max_digit = 9;

  for (int i = 0; i < max_digit
      && ((c = peekchar()) != EOF)
      && CHARCLASS[(int)c] == NUMERIC; ++i) {
    c = getchar();
    charval = (c - '0');
    int_num = int_num * 10 + charval;
  }

  // discard below numbers
  while ( (c = peekchar()) != EOF
      && CHARCLASS[(int)c] == NUMERIC) {
    getchar();
  }

  // max number nine digit
  while ( (int_num != 0) &&
      ! (100000000 <= int_num && int_num < 1000000000)) {
    int_num *= 10;
  }

  return int_num;
}


/* Get and convert unsigned numbers of all types. */
/* Read numbers assume that it is an integer */
/* When it meets point or 'e', go to the float process */
TOKEN number_original (TOKEN tok) {
  long int_num, below_point;
  double real_num;
  int c, cc, i;

  bool is_int = true;
  bool is_int_overflowed = false;

  int_num = get_integer_from_input(&is_int_overflowed);
  real_num = int_num;

  /* floating point process */
  c = peekchar();
  if (c == '.') {
    /* check the case of .. */
    cc = peek2char();
    if (cc == '.') {
      /* do nothing. number ends */

    } else if (CHARCLASS[cc] == NUMERIC){
      /* Calculate under decimal point number */
      /* only nine digit */
      is_int = false;

      /* remove point */
      getchar();

      below_point = get_nine_digit_integer();
      real_num += below_point / 1000000000.0; /* nine digit */
      c = peekchar();
    } else {
      /* after ., next char must be number */
      fprintf(stderr, "Invalid floating number form.\n");
      *((int*)0) = 0;
    }
  }
  
  if (c == 'e') {
    long exp;
    is_int = false;

    getchar();
    c = peekchar();

    if (c == '-') {
      /** when exp is negative */
      getchar();
      exp = get_integer_from_input(NULL);
      for (i = 0; i < exp; ++i) {
        real_num /= 10;
        if (real_num < FLT_MIN) {
          fprintf(stderr, "Floating number underflow detected\n");
          goto real_err;
        }
      }

    } else if (c == '+' || CHARCLASS[(int)c] == NUMERIC) {
      /** when exp is positive  */
      if (c == '+') {
        getchar();
      }
      exp = get_integer_from_input(NULL);
      for (i = 0; i < exp; ++i) {
        real_num *= 10;
        if (real_num > FLT_MAX) {
          fprintf(stderr, "Floating number overflow detected\n");
          goto real_err;
        }
      }
    } else {
      fprintf(stderr, "Float number format is incorrect\n");
      *((int*)0) = 0;
    }
  }
  /** floating point process end */


  if (is_int && is_int_overflowed) {
    fprintf(stderr, "Integer overflow is occurred.\n");
    goto int_err;
  }


  tok->tokentype = NUMBERTOK;

  if (is_int) {
    tok->basicdt = INTEGER;
    tok->intval = int_num;
  } else {
    tok->basicdt = REAL;
    tok->realval = real_num;
  }

  return (tok);


int_err:
  tok->tokentype = NUMBERTOK;
  tok->basicdt = INTEGER;
  tok->intval = int_num;
  return (tok);


real_err:
  tok->tokentype = NUMBERTOK;
  tok->basicdt = REAL;
  tok->realval = real_num;
  return (tok);
}




TOKEN number (TOKEN tok) {
  static char num_buff[NUM_BUFF_MAX];
  int num_buff_idx = 0, charval, i;
  long int_num = 0;
  double real_num = 0.0;
  char c, cc;
  bool is_int = true;
  bool has_point = false;
  bool has_e = false;
  bool is_int_overflowed = false;

  memset(num_buff, 0, sizeof(num_buff));
  
  for (num_buff_idx = 0; num_buff_idx < NUM_BUFF_MAX; ++num_buff_idx) {
    c = peekchar();
    cc = peek2char();

    if ( !(c == '.' && cc == '.') /* not '..' */
        && (CHARCLASS[(int)c] == NUMERIC  /* number or other chars*/
          || c == '.' || c == 'e' || c == '+' || c == '-')) {

      if ( (c == '+' || c == '-') && num_buff[num_buff_idx - 1] != 'e') {
        // - or + is an operator.
        // There is no case that num_buff_idx - 1 is zero
        // because first character must be numeric.
        break;
      }


      if (c == '.' || c == 'e') {
        is_int = false;
        if (c == '.') {
          has_point = (c == '.');
        } else if (c == 'e') {
          has_e = (c == 'e');
        }
      }


      // store character fo buffer.
      num_buff[num_buff_idx] = c;
      getchar();
    } else {
      break;
    }
  }

  printf("Number: %s, has_point: %d, has_e: %d\n", num_buff, has_point, has_e);


  tok->tokentype = NUMBERTOK;

  if (is_int) {
    for (i = 0; i < num_buff_idx; ++i) {
      charval = (num_buff[i] - '0');
      int_num = int_num * 10 + charval;

      if (int_num > INT_MAX) {
        is_int_overflowed = true;
      }
    }

    if (is_int_overflowed) {
      fprintf(stderr, "Integer overflow is occurred.\n");
    }

    tok->basicdt = INTEGER;
    tok->intval = int_num;
  } else {
    int exponent = 0;
    int exponent_after_e = 0;
    int sign = 1;
    bool not_zero_digit_found = false;
    int not_zero_digit_idx;
    int point_idx;
    int max_digit_idx;
    long mantissa = 0;

    /* get mantissa at most nine digit */
    /* find the first digit which is not zero */

    for (i = 0; i < num_buff_idx; ++i) {
      if (num_buff[i] == '.') {
        point_idx = i;
        continue;
      } else if (not_zero_digit_found == false
          && num_buff[i] == '0') {
        continue;
      }

      not_zero_digit_idx = i;
      not_zero_digit_found = true;
      break;
    }

    /* nine digit */
    max_digit_idx = i + 9;
    for (; i < max_digit_idx
        && i < num_buff_idx; ++i) {
      if (num_buff[i] == 'e') {
        break;
      }

      if (num_buff[i] == '.') {
        continue;
      }

      mantissa = mantissa * 10 + (num_buff[i] - '0');
    }
    printf("mantissa: %ld\n", mantissa);


    /* get exponent */
    if (has_point) {
      /* TODO */
    } else {
      for (i = not_zero_digit_idx; i < num_buff_idx; ++i) {
        if (num_buff[i] == 'e') {
          break;
        }
        exponent++;
      }

      /* -1... */
      if (exponent > 0) {
        exponent--;
      }
    }


    if (has_e) {
      /* find e and get exponent */
      for (i = num_buff_idx - 1; i >= 0 ; --i) {
        if (num_buff[i] == 'e') {
          break;
        }
      }

      i++;

      if (num_buff[i] == '-' || num_buff[i] == '+') {
        sign = num_buff[i] == '-' ? (-1) : 1;
        i++;
      }

      for (; i < num_buff_idx; i++) {
        exponent_after_e = exponent_after_e * 10 + (num_buff[i] - '0');
      }

      exponent_after_e *= sign;
    }

    exponent += exponent_after_e;
    printf("exp: %d\n", exponent);

    tok->basicdt = REAL;
    tok->realval = 12.34;
  }

  return (tok);
}
