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
#define MAX_CHAR 16
#define NUM_BUFF_MAX 1026

#define PE do{fprintf(stderr, "ERROR: ");}while(0)

#define FLT_MIN 1.175494e-38
#define FLT_MAX 3.402823e+38

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
        PE;
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
        && (CHARCLASS[(int)c] == ALPHA || CHARCLASS[(int)c] == NUMERIC) ) {
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
      PE;
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
    PE;
    fprintf(stderr, "No matching token type of the character: %c\n", c);
    *((int*)0) = 0;
  }

  return tok;
}


/** divide process: Integer process, Floating Process */

void get_mantissa(char *mantissa, int *mantissa_idx,
    char* num_buff, int first_non_zero_idx) {
  int i;
  memset(mantissa, 0, sizeof(char) * NUM_BUFF_MAX);

  for (i = first_non_zero_idx, *mantissa_idx = 0;
      i < NUM_BUFF_MAX;
      ++i) {
    if (num_buff[i] == '.') {
      continue;
    } else if (CHARCLASS[(int)num_buff[i]] != NUMERIC) {
      break;
    }

    mantissa[(*mantissa_idx)++] = num_buff[i];
  }
}

long get_exponent(char* num_buff, int num_buff_idx,
    int point_idx, int first_non_zero_idx,
    bool has_e, bool has_point) {

  int distance_bet_first_and_point = 0;

  long exponent = 0;
  long exponent_after_e = 0;
  int sign = 1;
  int i;


  /* calculate exponent by
   * subtracting the position of point and first non zero number */

  if (has_point) {
    distance_bet_first_and_point = point_idx - first_non_zero_idx;
    if (distance_bet_first_and_point > 0) {
      distance_bet_first_and_point--;
    }
    exponent += distance_bet_first_and_point;

    /** printf("distance_bet_first_and_point = %d\n", */
    /**     distance_bet_first_and_point); */
  } else {
    /* when a number has no point */
    for (i = first_non_zero_idx; i < num_buff_idx; ++i) {
      if (num_buff[i] == 'e') {
        break;
      }
      exponent++;
    }

    /* -1 because of the property of exponent */
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

      if (exponent_after_e > 2147483647) {
        exponent_after_e = 2147483647;
        break;
      }
    }

    exponent_after_e *= sign;
  }

  exponent += exponent_after_e;

  return exponent;
}


/* get integer part, mantissa, and exponent from the input */
TOKEN number (TOKEN tok) {
  static char num_buff[NUM_BUFF_MAX];
  int num_buff_idx = 0, charval, i;
  int int_num = 0;
  double real_num = 0.0;
  char c, cc;
  bool is_int = true;
  bool has_point = false;
  bool has_e = false;
  bool is_int_overflowed = false;

  bool is_met_first_non_zero_idx = false;
  int first_non_zero_idx;
  int point_idx;

  bool num_is_zero = false;

  memset(num_buff, 0, sizeof(num_buff));

  ///////////////// Start of reading number from stdin //////////////////
  for (num_buff_idx = 0; num_buff_idx < NUM_BUFF_MAX; ++num_buff_idx) {
    /* check break cases */
    c = peekchar();

    if (is_blank_or_whitespace(c) || c == EOF) {
      break;
    }

    cc = peek2char();

    if ((c == '.' && cc == '.')) {
      break;
    }

    // number characters
    if ( ! (CHARCLASS[(int)c] == NUMERIC
          || c == '.' || c == 'e' || c == '+' || c == '-') ) {
      break;
    }

    if ( (c == '+' || c == '-') && num_buff[num_buff_idx - 1] != 'e') {
      // - or + is an operator.
      // There is no case that num_buff_idx - 1 is zero
      // because first character must be numeric.
      break;
    }
    /* break cases end */

    if (c == '.' || c == 'e') {
      is_int = false;
      if (c == '.') {
        has_point = (c == '.');
        point_idx = num_buff_idx;
      } else if (c == 'e') {
        has_e = (c == 'e');

        if (is_met_first_non_zero_idx == false) {
          /* case when the number is zero */
          num_is_zero = true;
        }
      }
    }

    if (is_met_first_non_zero_idx == false
        && CHARCLASS[(int)c] == NUMERIC
        && c != '0') {

      first_non_zero_idx = num_buff_idx;
      is_met_first_non_zero_idx = true;
    }


    // store character fo buffer.
    num_buff[num_buff_idx] = c;
    getchar();
  }
  ///////////////// End of reading number from stdin //////////////////

  tok->tokentype = NUMBERTOK;
  /* when case of 0 or 0.0 */
  if (num_is_zero || is_met_first_non_zero_idx == false) {
    if (is_int) {
      tok->intval = 0;
      tok->basicdt = INTEGER;
    } else {
      tok->realval = 0;
      tok->basicdt = REAL;
    }
    return (tok);
  }


  if (is_int) {
    /* when a number is integer */
    int old_int_num;
    for (i = 0; i < num_buff_idx; ++i) {
      charval = (num_buff[i] - '0');
      old_int_num = int_num;
      int_num = int_num * 10 + charval;

      if (old_int_num > int_num) {
        is_int_overflowed = true;
      }
    }

    if (is_int_overflowed) {
      PE;
      fprintf(stderr, "Integer overflow is occurred.\n");
    }

    tok->basicdt = INTEGER;
    tok->intval = int_num;
  } else {
    /* floating number */

    /* 1. get integer part and mantissa
     * 2. get exponent 
     * 3. make a floating number from above information */


    /* get integer part and mantissa */
    static char mantissa[NUM_BUFF_MAX];
    int mantissa_idx;

    get_mantissa(mantissa, &mantissa_idx, num_buff, first_non_zero_idx);

    /* choose the place of point */
    /* get exponent */
    long exponent = get_exponent(num_buff, num_buff_idx,
        point_idx, first_non_zero_idx, 
        has_e, has_point);

    /* make a integer part and mantissa */
    real_num = mantissa[0] - '0';
    double exp_for_mant = 1;
    for (i = 1; i < mantissa_idx; ++i) {
      exp_for_mant /= 10.0;
      real_num += (mantissa[i] - '0') * exp_for_mant;
    }

    /* Apply exponent to the floating number */
    if (exponent > 0) {
      for (i = 0; i < exponent; ++i) {
        real_num *= 10;
        if (real_num > FLT_MAX) {
          PE;
          fprintf(stderr, "Floating number overflow occurred.\n");
          real_num = 1.0 / 0.0; // infinity
          break;
        }
      }
    } else if (exponent < 0) {
      for (i = exponent; i < 0; ++i) {
        real_num /= 10;
        if (real_num < FLT_MIN) {
          PE;
          fprintf(stderr, "Floating number underflow occurred.\n");
          real_num = 0.0;
          break;
        }
      }
    }

    tok->basicdt = REAL;
    tok->realval = real_num;
  }

  return (tok);


}
