#include <assert.h>
#include <iostream>
#include <cstdio>
#include <vector>
#include <cstdlib>
#include <time.h>
#include <math.h>
#include <algorithm>
#include "sat.h"
using namespace std;

#define MAX_VAR_COUNT                 1000//max:1000
#define start_var_table_idx                1
#define end_var_table_idx    (max_var_name+1)
#define UNIQUE_MODE                      0xF
#define DECISION_MODE                   0xF0
#define CONFLICT_MODE                  0xF00//meaning that this is second decision
#define INITIAL_MODE                  0xF000//is the clause only has one var

#define AVAILABLE_VAR_SHIFT                0
#define AVAILABLE_CLAUSE_SHIFT             8
#define AVAILABLE_VAR_MASK              0xFF
//#define AVAILABLE_CLAUSE_NEGATIVE_BIT    0x800000000
#define AVAILABLE_CLAUSE_NEGATIVE_BIT    0xFF000000
vector<uint32_t> unpicked_table;
bool CONFLICT_IN_ADD_DECISION = false;

#define FAILED_FIND_POSSIBLE_TARGET       -1

#define UNDECIDED_VAR_NAME                -1

uint32_t max_var_name = 0;
vector<vector<int> > input_clause;
var *var_table;//use var_name to access it, not index(meaning start from 1)
vector<int> var_postive_watched_clause_table[MAX_VAR_COUNT];//use var_name to record,not "index"
vector<int> var_negative_watched_clause_table[MAX_VAR_COUNT];
vector<decision*> decision_queue;
vector<decision*> record_decided_decision;
#define MAGIC_DECISION 0x78123456
uint32_t first_decision_var = MAGIC_DECISION;
bool end_solving = false;


static bool verify_result(void);
static void back_tracking(void);

static bool var_exist(int var)
{
    int var_pos = (int)abs(var);
    if(var_table[var_pos].var_name == 0)/*due to table is zero-initialized*/
    {
        return false;
    }else
    {
        return true;
    }
}

/*search all clause to create var table*/
void build_var_table(void)
{
    var_table = (var*)(calloc(end_var_table_idx-start_var_table_idx+1,sizeof(var)));/*zero initialize*/
    int var_pos;
    for(uint32_t i = 0;i < input_clause.size();i++)
    {
        for(uint32_t j = 0;j < input_clause[i].size();j++)
        {
            if(!var_exist(input_clause[i][j]))
            {
                var_pos = (int)abs(input_clause[i][j]);
                var_table[var_pos].var_name = var_pos;
                var_table[var_pos].value = VAL_UNASSIGNED;
            }
        }
    }
    for(uint32_t i = start_var_table_idx;i < end_var_table_idx;i++)
    {
        unpicked_table.push_back(i);
    }
}

static void init_two_watching_literal(uint32_t var_name,uint32_t src_idx,uint32_t clause_idx)
{
    if(input_clause[clause_idx][src_idx] > 0)
    {
        var_postive_watched_clause_table[var_name].push_back(clause_idx);
    }
    if(input_clause[clause_idx][src_idx] < 0)
    {
        var_negative_watched_clause_table[var_name].push_back(clause_idx);
    }
}

static inline void add_decision_queue(uint32_t var_name,int value,int mode)
{
    CONFLICT_IN_ADD_DECISION = false;
    assert(value != VAL_UNASSIGNED);
    for(uint32_t i = 0;i < decision_queue.size();i++)
    {
        if(decision_queue[i]->variable.var_name == var_name)
        {
            if(decision_queue[i]->variable.value != value)
            {
                for(uint32_t j = 0;j < decision_queue.size();j++)
                {
                    free(decision_queue[j]);
                }
                decision_queue.clear();
                back_tracking();
                CONFLICT_IN_ADD_DECISION = true;
                return;
            }else
            {
                return;
            }
        }
    }
    decision *p2decision = (decision*)malloc(sizeof(decision));
    p2decision->variable.var_name = var_name;
    p2decision->variable.value = value;
    p2decision->mode = mode;
    switch(mode)
    {
        case UNIQUE_MODE:
        case DECISION_MODE:
        case INITIAL_MODE:
            decision_queue.push_back(p2decision);
            break;
        case CONFLICT_MODE:
            decision_queue.insert(decision_queue.begin(),p2decision);
            break;
        default:
            fprintf(stderr,"UNKNOWN mode to add decision queue\n");
            exit(EXIT_FAILURE);
            break;
    }
}

static inline void pop_from_decision_queue(void)
{
    decision *p2decision;
    p2decision = decision_queue.back();
    decision_queue.pop_back();
    free(p2decision);
}

void init_solver(void)
{
    uint32_t watched_var_1,watched_var_2;
    for(uint32_t i = 0;i < input_clause.size();i++)
    {
        if(input_clause[i].size() > 1)
        {
            /*TODO:random pick*/
            watched_var_1 = (uint32_t)abs(input_clause[i][0]);
            watched_var_2 = (uint32_t)abs(input_clause[i][1]);
            init_two_watching_literal(watched_var_1,0,i);
            init_two_watching_literal(watched_var_2,1,i);
        }else
        {
            watched_var_1 = (uint32_t)abs(input_clause[i][0]);
            if(input_clause[i][0] > 0)
            {
                add_decision_queue(watched_var_1,VAL_1,INITIAL_MODE);
            }else
            {
                add_decision_queue(watched_var_1,VAL_0,INITIAL_MODE);
            }
        }
    }
}


/*return true if successful*/
static bool make_decision(void)
{
    int var = UNDECIDED_VAR_NAME;
    vector<int>::iterator it;
    int value;
    if(end_solving)
    {
        return false;
    }
    for(int i = (int)start_var_table_idx;i < (int)end_var_table_idx;i++)
    {
        //unassigned
        if(var_table[i].value == VAL_UNASSIGNED)
        {
            //unassigned + watched
            if((var_postive_watched_clause_table[i].size() + var_negative_watched_clause_table[i].size()) > 0)
            {
                var = var_table[i].var_name;
                if(first_decision_var == MAGIC_DECISION)
                {
                     first_decision_var = i;//if back track to this var,UNSAT
                }
                break;

                /*
                //unassigned + watched + unpicked
                for(uint32_t j = 0;j < unpicked_table.size();j++)
                {
                    if(unpicked_table[j] == var_table[i].var_name)
                    {
                        var = var_table[i].var_name;
                        unpicked_table.erase(unpicked_table.begin()+j);
                        if(first_decision_var == MAGIC_DECISION)
                        {
                            first_decision_var = i;//if back track to this var,UNSAT
                        }
                        end_loop = true;
                        break;
                    }
                }
                */
            }
        }
        /*
        if(end_loop)
        {
            break;
        }
        */
    }
    if(var == UNDECIDED_VAR_NAME)
    {
        return false;
    }
    if(var_postive_watched_clause_table[var].size() > 0)
    {
        value = VAL_1;
    }else
    {
        value = VAL_0;
    }
    add_decision_queue((uint32_t)var,value,DECISION_MODE);
    return true;
}

static inline uint32_t find_the_other_watched_var(uint32_t var_name,int clause_idx)
{
    int possible_var_name;
    vector<uint32_t> candidate_var;
    //NOTE: watched var may be assigned
    //get the other watched var
        // search all var's watched-list,to get 
    for(uint32_t i = 0;i < input_clause[clause_idx].size();i++)
    {
        possible_var_name = (int)abs(input_clause[clause_idx][i]);
        for(uint32_t j = 0;j < var_postive_watched_clause_table[possible_var_name].size();j++)
        {
            if(var_postive_watched_clause_table[possible_var_name][j] == clause_idx)
            {
                candidate_var.push_back(possible_var_name);
            }
        }
        for(uint32_t j = 0;j < var_negative_watched_clause_table[possible_var_name].size();j++)
        {
            if(var_negative_watched_clause_table[possible_var_name][j] == clause_idx)
            {
                candidate_var.push_back(possible_var_name);
            }
        }
    }
    possible_var_name = UNDECIDED_VAR_NAME;
    assert(candidate_var.size() == 2);//one of watched is assigned,so only left one here
    for(uint32_t i = 0;i < candidate_var.size();i++)
    {
        if(candidate_var[i] != var_name)
        {
            possible_var_name = candidate_var[i];
        }
    }
    assert(possible_var_name != UNDECIDED_VAR_NAME);
    return possible_var_name;
}

static inline int find_unwatched_unassigned_var(uint32_t watched_var_1,uint32_t watched_var_2,uint32_t current_clause)
{
    uint32_t var_name;
    for(uint32_t i =0;i < input_clause[current_clause].size();i++)
    {
        var_name = (uint32_t)abs(input_clause[current_clause][i]);
        if((var_name != watched_var_1) && 
           (var_name != watched_var_2) )
        {
            if(var_table[var_name].value == VAL_UNASSIGNED)
            {
                return var_table[var_name].var_name;
            }
        }
    }
    return UNDECIDED_VAR_NAME;
}

//There are many strategies,now simply return the first one.
static inline int find_watched_unassigned_var()
{
    for(uint32_t i = start_var_table_idx;i < end_var_table_idx;i++)
    {
        if(var_table[i].value == VAL_UNASSIGNED)
        {
            if((var_postive_watched_clause_table[i].size() + var_negative_watched_clause_table[i].size()) > 0)
            {
                return i;
            }
        }
    }
    return UNDECIDED_VAR_NAME;
}

static inline uint32_t get_var_name_in_clause(uint32_t clause_idx,uint32_t var_idx)
{
    return (uint32_t)abs(input_clause[clause_idx][var_idx]);
}

//for case 3 specifically
static inline bool is_unit_clause(uint32_t clause_idx)
{
    bool result = false;
    for(uint32_t i = 0;i < input_clause[clause_idx].size();i++)
    {
        if(input_clause[clause_idx][i] > 0)// postive clause
        {
            if(var_table[get_var_name_in_clause(clause_idx,i)].value == VAL_1)
            {
                result = true;
                break;
            }
        }else//negative clause
        {
            if(var_table[get_var_name_in_clause(clause_idx,i)].value == VAL_0)
            {
                result = true;
                break;
            }
        }
    }
    return result;
}
static inline bool is_input_clause_var_postive(uint32_t clause_idx,uint32_t var_name)
{
    int var_idx = -1;
    for(uint32_t i = 0;i < input_clause[clause_idx].size();i++)
    {
        if((uint32_t)abs(input_clause[clause_idx][i]) == var_name)
        {
            var_idx = i;
        }
    }
    if(var_idx == -1)
    {
        fprintf(stderr,"this clause do not have this var\n");
        exit(EXIT_FAILURE);
    }
    if(input_clause[clause_idx][var_idx] > 0)
    {
        return true;
    }else
    {
        return false;
    }
}

static void back_tracking(void)
{
    uint32_t last_var_1,last_var_2;
    uint32_t mode;
    int value = VAL_UNASSIGNED;
    decision *p2decision;
    //remove previous decision in this action
    decision_queue.clear();

    if(record_decided_decision.back()->mode == CONFLICT_MODE)
    {
        while(!record_decided_decision.empty())
        {
            //pop last two var(same) in record,and assign it to be unassigned
            p2decision = record_decided_decision.back();
            last_var_1 = p2decision->variable.var_name;
            record_decided_decision.pop_back();
            free(p2decision);

            p2decision = record_decided_decision.back();
            last_var_2 = p2decision->variable.var_name;
            record_decided_decision.pop_back();
            free(p2decision);

            assert(last_var_1 == last_var_2);
            var_table[last_var_1].value = VAL_UNASSIGNED;
            if(last_var_1 == first_decision_var)
            {
                end_solving = true;
                return;
            }

            if(!record_decided_decision.empty())
            {
                //get var until it is not UNIQUE_MODE
                p2decision = record_decided_decision.back();
                mode = p2decision->mode;
                while(mode == UNIQUE_MODE)
                {
                    var_table[p2decision->variable.var_name].value = VAL_UNASSIGNED;
                    record_decided_decision.pop_back();
                    free(p2decision);
                    if(!record_decided_decision.empty())
                    {  
                        p2decision = record_decided_decision.back();
                        mode = p2decision->mode;
                    }
                }
                //check this var is second assignment or not
                if(mode == CONFLICT_MODE)
                {
                    continue;
                }else// DECISION_MODE,make its second assignment
                {
                    last_var_1 = p2decision->variable.var_name;
                    value = var_table[last_var_1].value;
                    assert(value != VAL_UNASSIGNED);
                    if(value == VAL_0)
                    {
                        value = VAL_1;
                    }else
                    {
                        value = VAL_0;
                    }
                    add_decision_queue(last_var_1,value,CONFLICT_MODE);
                    return;
                }
            }
        }
    }else// UNIQUE_MODE or DECISION_MODE but conflict
    {
        while(!record_decided_decision.empty())
        {
            //get var until it is not UNIQUE_MODE
            p2decision = record_decided_decision.back();
            mode = p2decision->mode;
            while(mode == UNIQUE_MODE)
            {
                var_table[p2decision->variable.var_name].value = VAL_UNASSIGNED;
                record_decided_decision.pop_back();
                free(p2decision);
                if(!record_decided_decision.empty())
                {  
                    p2decision = record_decided_decision.back();
                    mode = p2decision->mode;
                }else
                {
                }
            }
            if(mode == DECISION_MODE)
            {
                last_var_1 = p2decision->variable.var_name;
                value = var_table[last_var_1].value;
                assert(value != VAL_UNASSIGNED);
                if(value == VAL_0)
                {
                    value = VAL_1;
                }else
                {
                    value = VAL_0;
                }
                add_decision_queue(last_var_1,value,CONFLICT_MODE);
                return;
            }else if(mode == CONFLICT_MODE)
            {
                back_tracking();
                return;
            }else// Initial mode
            {
                end_solving = true;
                return;
                //fprintf(stderr,"back tracking error\n");
                //exit(EXIT_FAILURE);
            }
        }
    }
    
}

//main algorithm for two-literal watching
static void update_two_watching_literal(decision *p2decision)
{
    vector<int> *need_new_decision_clause_list;
    int the_other_watched_var;
    int new_watched_var;
    int unwatched_unassigned_var;
    int idx;
    uint32_t current_clause;
    int loop_size;
    if(p2decision->variable.value == VAL_1)
    {
        need_new_decision_clause_list = &var_negative_watched_clause_table[p2decision->variable.var_name];
    }else if(p2decision->variable.value == VAL_0)
    {
        need_new_decision_clause_list = &var_postive_watched_clause_table[p2decision->variable.var_name];
    }else
    {
        fprintf(stderr,"This decision value is undecided yet!\n");
    }

    /*4 cases*/
    loop_size = (int)need_new_decision_clause_list->size();
    for(int i = 0;i < loop_size;i++)
    {
        current_clause = (*need_new_decision_clause_list)[i];
        the_other_watched_var = find_the_other_watched_var(p2decision->variable.var_name,current_clause);
        // CASE 1:
        if( (unwatched_unassigned_var = find_unwatched_unassigned_var(p2decision->variable.var_name,the_other_watched_var,current_clause))
                    != UNDECIDED_VAR_NAME )
        {
            //add this var be the new watched var in the clause
            idx = -1;
            new_watched_var = unwatched_unassigned_var;
            for(uint32_t j = 0;j < input_clause[current_clause].size();j++)
            {
                if((int)abs(input_clause[current_clause][j]) ==  new_watched_var)
                {
                    idx = j;//the new_watched_var index in input_clause
                    break;
                }
            }
            assert(idx != -1);
            if(input_clause[current_clause][idx] > 0)
            {
                var_postive_watched_clause_table[new_watched_var].push_back(current_clause);
            }else
            {
                var_negative_watched_clause_table[new_watched_var].push_back(current_clause);
            }
            //remove the old watched var from the clause
            need_new_decision_clause_list->erase(need_new_decision_clause_list->begin()+i);
            i--;//due to remove one clause,the idx need to remain same;
            loop_size = (uint32_t)need_new_decision_clause_list->size();//update loop size

        }else if( is_unit_clause(current_clause))//case 3
        {
            //do nothing
            continue;
        }else if(var_table[the_other_watched_var].value == VAL_UNASSIGNED)//case 2
        {
            int value = VAL_UNASSIGNED;
            if(is_input_clause_var_postive(current_clause,the_other_watched_var))
            {
                value = VAL_1;
            }else
            {
                value = VAL_0;
            }
            add_decision_queue(the_other_watched_var,value,UNIQUE_MODE);
            if(CONFLICT_IN_ADD_DECISION)
            {
                return;
            }
        }else//case 4(conflict)
        {

            if(record_decided_decision.back()->mode == CONFLICT_MODE)//second conflict
            {
                back_tracking();
                return;
            }else//first conflict
            {
                int current_value = record_decided_decision.back()->variable.value;
                int reverse_value;
                if(record_decided_decision.back()->mode == UNIQUE_MODE)
                {
                    back_tracking();
                    return;
                }
                if(current_value == VAL_0)
                {
                    reverse_value = VAL_1;
                }else
                {
                    reverse_value = VAL_0;
                }
                add_decision_queue(record_decided_decision.back()->variable.var_name,reverse_value,CONFLICT_MODE);
            }
            return;
        }
    }

}

static inline void print_result(void)
{
    for(uint32_t i = start_var_table_idx;i < end_var_table_idx;i++)
    {
        if(var_table[i].value == VAL_1)
        {
            printf("%d ",i);
        }else if(var_table[i].value == VAL_0)
        {
            printf("-%d ",i);
        }else
        {
            fprintf(stderr,"OUTPUT result error!\n");
            exit(EXIT_FAILURE);
        }
    }
}

static bool verify_result(void)
{
    bool result = false;
    bool clause_result = false;
    int loop_size  = (uint32_t)input_clause.size();

    for(int i = 0;i < loop_size;i++)
    {
        clause_result = false;
        for(uint32_t j = 0;j < input_clause[i].size();j++)
        {
            if(var_table[abs(input_clause[i][j])].value == VAL_0)
            {
                if(input_clause[i][j] < 0)
                {
                    clause_result = true;
                }
            }else if(var_table[abs(input_clause[i][j])].value == VAL_1)
            {
                if(input_clause[i][j] > 0)
                {
                    clause_result = true;
                }
            }else//unassigned
            {
                result = false;
            }
        }
        if(!clause_result)
        {
            return false;
        }
        input_clause.erase(input_clause.begin() + i);
        i--;
        loop_size = input_clause.size();
    }
    if(input_clause.empty())
    {
        result = true;
    }else
    {
        result = false;
    }
    return result;
}

void solver(void)
{
    srand(time(NULL));
    decision *p2decision;
    while(1)
    {
        if(decision_queue.empty())
        {
            /*find a decision*/
            if(!make_decision())/*if no other decision could make*/
            {
                if(!verify_result())
                {
                    printf("s UNSATISFIABLE\n");
                    return;
                }else
                {
                    printf("s SATISFIABLE\n");
                    printf("v ");
                    print_result();
                    printf("0\n");
                    return;
                }
            }else
            {
                //do nothing:find a decision
            }
        }else//doing work based on decision_queue
        {
            while(!decision_queue.empty())
            {
                p2decision = decision_queue.front();
                assert(p2decision->variable.value != VAL_UNASSIGNED);
                record_decided_decision.push_back(p2decision);
                decision_queue.erase(decision_queue.begin());//not actually destroy the first element,only the reference
            
                var_table[p2decision->variable.var_name].value = p2decision->variable.value;
                update_two_watching_literal(p2decision);
            }
        }
    }
}

int main(int argc,char *argv[])
{
    /*read cnf file*/
    int max_name;
    parse_DIMACS_CNF(input_clause,max_name,argv[1]);
    max_var_name = (uint32_t)max_name;
    /*build var_table for management*/
    build_var_table();
    /*traverse all clause to initialize the initial two watched var for each and unique decision*/
    init_solver();
    /*main algorithm*/
    solver();

    /*clean up*/
    //assert(decision_queue.empty());
    while(!record_decided_decision.empty())
    {
        free(record_decided_decision.back());
        record_decided_decision.pop_back();
    }
    free(var_table);
    return 0;
}
