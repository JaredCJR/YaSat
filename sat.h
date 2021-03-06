#ifndef __SAT_H
#define __SAT_H

#include "parser.h"
#include <cstdint>

#define VAL_UNASSIGNED      -99
#define VAL_1                1
#define VAL_0                0

typedef struct var{
    uint32_t var_name;
    int value;
    int decision_level;
    int decision_clause;
    uint32_t VSIDS_count;
}var; 

typedef struct decision{
    var variable;
    int mode;
}decision;

#endif
