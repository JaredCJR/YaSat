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

#define MAX_VAR_COUNT                 2000//max:2000
#define start_var_table_idx                1
#define end_var_table_idx    (max_var_name+1)
#define UNIQUE_MODE                      0xF
#define DECISION_MODE                   0xF0
#define CONFLICT_MODE                  0xF00//meaning that this is second decision
#define START_SYMBOL_MODE             0xF000//if there is clause only has one var


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
uint32_t current_level;
bool IS_FirstUIP_RETRY = true;
vector<uint32_t> recorded_backtracking_level;
#define INITIAL_LEVEL  1 //only used in INITIAL_MODE(the clause only has one var)
#define START_LEVEL    INITIAL_LEVEL //only used in init_solver()
#define MAGIC_LEVEL   -87
#define LEVEL_UNASSIGNED -4
#define CLAUSE_UNASSIGNED -4
#define NO_IMPLIED_CLAUSE -1// decison node
bool NEW_UIP_resolve = true;
#define VSIDS_INIT           0
#define VSIDS_UPDATE_ADD     1
#define VSIDS_UPDATE_DELETE  2
vector<uint32_t> available_vars;

static bool verify_result(void);
static void back_tracking(int conflicting_clause);
void build_var_table(void);
void init_solver(void);

static bool var_exist(int var)
{
	int var_pos = (int)abs(var);
	if (var_table[var_pos].var_name == 0) { /*due to table is zero-initialized*/
		return false;
	} else {
		return true;
	}
}

/*search all clause to create var table*/
void build_var_table(void)
{
	var_table = (var*)(calloc(end_var_table_idx - start_var_table_idx + 1, sizeof(var))); /*zero initialize*/
	int var_pos;
	for (uint32_t i = 0; i < input_clause.size(); i++) {
		for (uint32_t j = 0; j < input_clause[i].size(); j++) {
			if (!var_exist(input_clause[i][j])) {
				var_pos = (int)abs(input_clause[i][j]);
				var_table[var_pos].var_name = var_pos;
				var_table[var_pos].value = VAL_UNASSIGNED;
				var_table[var_pos].decision_level = LEVEL_UNASSIGNED;
				var_table[var_pos].decision_clause = CLAUSE_UNASSIGNED;
				var_table[var_pos].VSIDS_count = VSIDS_INIT;
			}
		}
	}
}

static inline void update_VSIDS_counter(int var_name, int mode)
{
	assert(var_name != UNDECIDED_VAR_NAME);
	assert(var_name >= 0);
	if (mode == VSIDS_UPDATE_ADD) {
		var_table[var_name].VSIDS_count++;
	} else if (mode == VSIDS_UPDATE_DELETE) {
		if (var_table[var_name].VSIDS_count >= 1) {
			var_table[var_name].VSIDS_count--;
		} else {
			var_table[var_name].VSIDS_count = VSIDS_INIT;
		}
	} else {
		printf("error in update VSIDS\n");
		exit(EXIT_FAILURE);
	}
}

static void init_two_watching_literal(uint32_t var_name, uint32_t src_idx, uint32_t clause_idx)
{
	if (input_clause[clause_idx][src_idx] > 0) {
		var_postive_watched_clause_table[var_name].push_back(clause_idx);
	}
	if (input_clause[clause_idx][src_idx] < 0) {
		var_negative_watched_clause_table[var_name].push_back(clause_idx);
	}
	update_VSIDS_counter(var_name, VSIDS_UPDATE_ADD);
}

static inline void add_decision_queue(uint32_t var_name, int value, int mode, int decision_level, int decision_clause)
{
	decision *p2decision;
	assert(value != VAL_UNASSIGNED);
	p2decision = (decision*)malloc(sizeof(decision));
	p2decision->variable.var_name = var_name;
	p2decision->variable.value = value;
	p2decision->variable.decision_clause = decision_clause;
	p2decision->variable.decision_level = decision_level;
	p2decision->mode = mode;
	switch (mode) {
	case UNIQUE_MODE:
	case DECISION_MODE:
	case START_SYMBOL_MODE:
		decision_queue.push_back(p2decision);
		break;
	case CONFLICT_MODE:
		decision_queue.insert(decision_queue.begin(), p2decision);
		break;
	default:
		fprintf(stderr, "UNKNOWN mode to add decision queue\n");
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

static inline void add_watching_literal_for_clause(uint32_t clause_idx)
{
	int value;
	uint32_t watched_var_1, watched_var_2;
	if (input_clause[clause_idx].size() > 1) {
		watched_var_1 = (uint32_t)abs(input_clause[clause_idx][0]);
		watched_var_2 = (uint32_t)abs(input_clause[clause_idx][1]);
		init_two_watching_literal(watched_var_1, 0, clause_idx);
		init_two_watching_literal(watched_var_2, 1, clause_idx);
	} else {
		watched_var_1 = (uint32_t)abs(input_clause[clause_idx][0]);
		if (input_clause[clause_idx][0] > 0) {
			value = VAL_1;
		} else {
			value = VAL_0;
		}
		add_decision_queue(watched_var_1, value, START_SYMBOL_MODE, INITIAL_LEVEL, NO_IMPLIED_CLAUSE);
	}
}

void init_solver(void)
{
	current_level = START_LEVEL;
	for (uint32_t j = 0; j < decision_queue.size(); j++) {
		free(decision_queue[j]);
	}
	decision_queue.clear();
	for (uint32_t i = 0; i < input_clause.size(); i++) {
		add_watching_literal_for_clause(i);
	}
}


/*return true if successful*/
static bool make_decision(void)
{
	int var = UNDECIDED_VAR_NAME;
	vector<int>::iterator it;
	int value;
	if (end_solving) {
		return false;
	}
	available_vars.clear();
	for (int i = (int)start_var_table_idx; i < (int)end_var_table_idx; i++) {
		//unassigned
		if (var_table[i].value == VAL_UNASSIGNED) {
			//unassigned + watched
			if ((var_postive_watched_clause_table[i].size() + var_negative_watched_clause_table[i].size()) > 0) {
				available_vars.push_back(var_table[i].var_name);
			}
		}
	}
	uint32_t max_VSIDS = 0;
	int max_VSIDS_idx = 0;
	if (!available_vars.empty()) {
		for (uint32_t i = 0; i < available_vars.size(); i++) {
			if (var_table[available_vars[i]].VSIDS_count >= max_VSIDS) {
				max_VSIDS = var_table[available_vars[i]].VSIDS_count;
				max_VSIDS_idx = i;
			}
		}
		var = available_vars[max_VSIDS_idx];
		if (first_decision_var == MAGIC_DECISION) {
			first_decision_var = var;//if back track to this var,UNSAT
		}
	}
	if (var == UNDECIDED_VAR_NAME) {
		return false;
	}
	if (var_postive_watched_clause_table[var].size() > 0) {
		value = VAL_1;
	} else {
		value = VAL_0;
	}
	current_level++;
	add_decision_queue((uint32_t)var, value, DECISION_MODE, current_level, NO_IMPLIED_CLAUSE);
	return true;
}

static inline uint32_t find_the_other_watched_var(uint32_t var_name, int clause_idx)
{
	int possible_var_name;
	vector<uint32_t> candidate_var;
	//NOTE: watched var may be assigned
	//get the other watched var
	// search all var's watched-list,to get
	for (uint32_t i = 0; i < input_clause[clause_idx].size(); i++) {
		possible_var_name = (int)abs(input_clause[clause_idx][i]);
		for (uint32_t j = 0; j < var_postive_watched_clause_table[possible_var_name].size(); j++) {
			if (var_postive_watched_clause_table[possible_var_name][j] == clause_idx) {
				candidate_var.push_back(possible_var_name);
			}
		}
		for (uint32_t j = 0; j < var_negative_watched_clause_table[possible_var_name].size(); j++) {
			if (var_negative_watched_clause_table[possible_var_name][j] == clause_idx) {
				candidate_var.push_back(possible_var_name);
			}
		}
	}
	possible_var_name = UNDECIDED_VAR_NAME;
	assert(candidate_var.size() == 2);//one of watched is assigned,so only left one here
	for (uint32_t i = 0; i < candidate_var.size(); i++) {
		if (candidate_var[i] != var_name) {
			possible_var_name = candidate_var[i];
		}
	}
	assert(possible_var_name != UNDECIDED_VAR_NAME);
	return possible_var_name;
}

static inline int find_unwatched_unassigned_var(uint32_t watched_var_1, uint32_t watched_var_2, uint32_t current_clause)
{
	uint32_t var_name;
	for (uint32_t i = 0; i < input_clause[current_clause].size(); i++) {
		var_name = (uint32_t)abs(input_clause[current_clause][i]);
		if ((var_name != watched_var_1) &&
		    (var_name != watched_var_2)) {
			if (var_table[var_name].value == VAL_UNASSIGNED) {
				return var_table[var_name].var_name;
			}
		}
	}
	return UNDECIDED_VAR_NAME;
}

//There are many strategies,now simply return the first one.
static inline int find_watched_unassigned_var()
{
	for (uint32_t i = start_var_table_idx; i < end_var_table_idx; i++) {
		if (var_table[i].value == VAL_UNASSIGNED) {
			if ((var_postive_watched_clause_table[i].size() + var_negative_watched_clause_table[i].size()) > 0) {
				return i;
			}
		}
	}
	return UNDECIDED_VAR_NAME;
}

static inline uint32_t get_var_name_in_clause(uint32_t clause_idx, uint32_t var_idx)
{
	return (uint32_t)abs(input_clause[clause_idx][var_idx]);
}

//for case 3 specifically
static inline bool is_unit_clause(uint32_t clause_idx)
{
	bool result = false;
	for (uint32_t i = 0; i < input_clause[clause_idx].size(); i++) {
		if (input_clause[clause_idx][i] > 0) { // postive clause
			if (var_table[get_var_name_in_clause(clause_idx, i)].value == VAL_1) {
				result = true;
				break;
			}
		} else { //negative clause
			if (var_table[get_var_name_in_clause(clause_idx, i)].value == VAL_0) {
				result = true;
				break;
			}
		}
	}
	return result;
}
static inline bool is_input_clause_var_postive(uint32_t clause_idx, uint32_t var_name)
{
	int var_idx = -1;
	for (uint32_t i = 0; i < input_clause[clause_idx].size(); i++) {
		if ((uint32_t)abs(input_clause[clause_idx][i]) == var_name) {
			var_idx = i;
		}
	}
	if (var_idx == -1) {
		fprintf(stderr, "this clause do not have this var\n");
		exit(EXIT_FAILURE);
	}
	if (input_clause[clause_idx][var_idx] > 0) {
		return true;
	} else {
		return false;
	}
}

static inline bool is_at_least_two_var_assigned(uint32_t target_clause, int target_level)
{
	uint32_t count = 0;
	for (uint32_t i = 0; i < input_clause[target_clause].size(); i++) {
		if (var_table[abs(input_clause[target_clause][i])].decision_level == target_level) {
			count++;
		}
	}
	if (count >= 2) {
		return true;
	}
	return false;
}

static inline int find_lastest_assigned_var(int target_clause)
{
	for (uint32_t i = (record_decided_decision.size() - 1); i >= 0; i--) {
		for (uint32_t j = 0; j < input_clause[target_clause].size(); j++) {
			if (record_decided_decision[i]->variable.var_name == (uint32_t)abs(input_clause[target_clause][j])) {
				return record_decided_decision[i]->variable.var_name;
			}
		}
	}
	return UNDECIDED_VAR_NAME;
}

static inline uint32_t antecedent(uint32_t var_name)
{
	int clause = var_table[var_name].decision_clause;
	assert(clause != NO_IMPLIED_CLAUSE);
	return clause;
}


static inline uint32_t resolve(uint32_t clause_1, uint32_t clause_2, int var_name)
{
	vector<int> new_clause;
	new_clause.clear();
	bool same_var;
	for (uint32_t i = 0; i < input_clause[clause_1].size(); i++) {
		if (abs(input_clause[clause_1][i]) != var_name) {
			new_clause.push_back(input_clause[clause_1][i]);
		}
	}
	for (uint32_t i = 0; i < input_clause[clause_2].size(); i++) {
		same_var = false;
		if (abs(input_clause[clause_2][i]) != var_name) {
			for (uint32_t j = 0; j < new_clause.size(); j++) {
				if (new_clause[j] == input_clause[clause_2][i]) {
					same_var = true;
				}
			}
			if (!same_var) {
				new_clause.push_back(input_clause[clause_2][i]);
			}
		}
	}
	if (!NEW_UIP_resolve) {
		input_clause.back().clear();
		input_clause.pop_back();
	}
	NEW_UIP_resolve = false;
	assert(!new_clause.empty());
	input_clause.push_back(new_clause);
	return (input_clause.size() - 1);
}

//return the decision level that should back track to.
static uint32_t FirstUIP(uint32_t clause_idx, uint32_t level)
{
	int var_p;
	uint32_t result_clause = clause_idx;
	NEW_UIP_resolve = true;
	while (is_at_least_two_var_assigned(result_clause, level)) {
		var_p = find_lastest_assigned_var(result_clause);
		assert(var_p != UNDECIDED_VAR_NAME);
		result_clause = resolve(result_clause, antecedent(var_p), var_p);
	}
	return result_clause;
}

static inline void undo_var(uint32_t var_name)
{
	var_table[var_name].value = VAL_UNASSIGNED;
	var_table[var_name].decision_clause = CLAUSE_UNASSIGNED;
	var_table[var_name].decision_level = LEVEL_UNASSIGNED;
}

static inline void back_tracking_CONFLICT(void)
{
	int value;
	decision *p2decision = record_decided_decision.back();
	/*undo the conflict var*/
	undo_var(p2decision->variable.var_name);
	free(p2decision);
	record_decided_decision.pop_back();
	p2decision = record_decided_decision.back();
	free(p2decision);
	record_decided_decision.pop_back();
	while (!record_decided_decision.empty()) {
		p2decision = record_decided_decision.back();
		if (p2decision->mode == CONFLICT_MODE) {
            if(p2decision->variable.var_name == first_decision_var){
                end_solving = true;
                break;
            }
			/*undo the conflict var*/
			undo_var(p2decision->variable.var_name);
			free(p2decision);
			record_decided_decision.pop_back();
			p2decision = record_decided_decision.back();
			free(p2decision);
			record_decided_decision.pop_back();
		} else if (p2decision->mode == UNIQUE_MODE) {
			undo_var(p2decision->variable.var_name);
			free(p2decision);
			record_decided_decision.pop_back();
		} else if (p2decision->mode == DECISION_MODE) {
			if (p2decision->variable.value == VAL_1) {
				value = VAL_0;
			} else {
				value = VAL_1;
			}
			//TODO:
			uint32_t target_level = p2decision->variable.decision_level;
			IS_FirstUIP_RETRY = true;
			vector<uint32_t>::iterator it;
			it = find(recorded_backtracking_level.begin(), recorded_backtracking_level.end(), p2decision->variable.decision_level);
			if (it != recorded_backtracking_level.end()) {
				//Element found in myvector
				IS_FirstUIP_RETRY = false;
			} else {
				//Element not found in myvector
#ifdef debug
				printf("ADD:%d\n", target_level);
#endif
				recorded_backtracking_level.push_back(target_level);
			}
			//remove all recorded level until target is the last
			for (uint32_t i = 0; i < recorded_backtracking_level.size(); i++) {
				if (target_level < recorded_backtracking_level[i]) {
#ifdef debug
					printf("ERASE:%d\n", recorded_backtracking_level[i]);
#endif
					recorded_backtracking_level.erase(recorded_backtracking_level.begin() + i);
					i--;
				}
			}
			sort(recorded_backtracking_level.begin(), recorded_backtracking_level.end());
#ifdef debug
			printf("TARGET LEVEL = %d\n", target_level);
			printf("===========================\n");
			printf("recorded LEVEL seq: ");
			for (uint32_t i = 0; i < recorded_backtracking_level.size(); i++) {
				printf("%d ", recorded_backtracking_level[i]);
			}
			printf("\n");
			printf("===========================\n");
#endif
			if (IS_FirstUIP_RETRY) {
				current_level = p2decision->variable.decision_level;
				add_decision_queue(p2decision->variable.var_name, p2decision->variable.value, p2decision->mode, p2decision->variable.decision_level, p2decision->variable.decision_clause);
				free(p2decision);
				record_decided_decision.pop_back();
			} else {
				if (p2decision->variable.value == VAL_1) {
					value = VAL_0;
				} else {
					value = VAL_1;
				}
				current_level = p2decision->variable.decision_level;
				add_decision_queue(p2decision->variable.var_name, value, CONFLICT_MODE, p2decision->variable.decision_level, p2decision->variable.decision_clause);
			}
			//end new
			/*
			current_level = record_decided_decision.back()->variable.decision_level;
			add_decision_queue(record_decided_decision.back()->variable.var_name, value, CONFLICT_MODE, record_decided_decision.back()->variable.decision_level, record_decided_decision.back()->variable.decision_clause);
			*/
			return;
		} else {
			end_solving = true;
			return;
		}
	}
}

static void back_tracking(int conflicting_clause)
{
#ifdef debug
	printf("conflict var:%d , value:%d \n", record_decided_decision.back()->variable.var_name, record_decided_decision.back()->variable.value);
#endif
	int level = current_level;
	int max_level = MAGIC_LEVEL;
	int temp_level = MAGIC_LEVEL;
	decision *p2decision;
	decision *p2decision_past;
	bool loop_continue = false;
	int value;
	uint32_t var_name;
	int learned_clause = FirstUIP(conflicting_clause, level);
	bool NO_learned_clause = false;
	if (conflicting_clause == learned_clause) {
		NO_learned_clause = true;
	}
	for (uint32_t i = 0; i < input_clause[learned_clause].size(); i++) {
		temp_level = var_table[abs(input_clause[learned_clause][i])].decision_level;
		if ((temp_level != level) && (temp_level != INITIAL_LEVEL)) {
			if (temp_level > max_level) {
				max_level = temp_level;
			}
		}
	}
#ifdef debug
	printf("backtracking to LEVEL = %d\n", max_level);
	int debug_level = max_level;
#endif
	for (uint32_t j = 0; j < decision_queue.size(); j++) {
		free(decision_queue[j]);
	}
	decision_queue.clear();
	if (max_level == MAGIC_LEVEL) { /*back track to level 0(no assignment)*/
		while (!record_decided_decision.empty()) {
			if (record_decided_decision.back()->variable.decision_level != INITIAL_LEVEL) {
				p2decision = record_decided_decision.back();
				var_name = p2decision->variable.var_name;
				undo_var(var_name);
				free(p2decision);
				record_decided_decision.pop_back();
			} else {
				break;
			}
		}
		current_level = START_LEVEL;
		add_watching_literal_for_clause(input_clause.size() - 1);
		first_decision_var = MAGIC_DECISION;
		recorded_backtracking_level.clear();
	} else { /*back track to max_level */
		/*remove the learned_clause*/
		if (NO_learned_clause) {
			input_clause.back().clear();
			input_clause.pop_back();
		} else {
#ifdef debug
			printf("Learned clause: ");
			for (uint32_t i = 0; i < input_clause.back().size(); i++) {
				printf("%d ", input_clause[input_clause.size() - 1][i]);
			}
			printf("\n");
#endif
		}

		p2decision = record_decided_decision.back();
		if (max_level != p2decision->variable.decision_level) {
			loop_continue = true;
		}
		while (loop_continue) {
			/*loop until the first max_level var*/
			loop_continue = false;
			var_table[p2decision->variable.var_name].value = VAL_UNASSIGNED;
			var_table[p2decision->variable.var_name].decision_level = LEVEL_UNASSIGNED;
			var_table[p2decision->variable.var_name].decision_clause = CLAUSE_UNASSIGNED;
			free(p2decision);
			record_decided_decision.pop_back();
			//next iteration?
			if (!record_decided_decision.empty()) {
				p2decision = record_decided_decision.back();
				if (max_level != p2decision->variable.decision_level) {
					loop_continue = true;
				}
			} else {
				printf("ERROR in back_tracking to target level\n");
				exit(EXIT_FAILURE);
			}
		}
		//back track to the head of this level decision
		while (1) {
			if (record_decided_decision.size() >= 2) {
				p2decision_past = record_decided_decision.back();
				p2decision = record_decided_decision[record_decided_decision.size() - 2];
				if (p2decision->variable.decision_level == max_level) {
					if (p2decision->variable.var_name == p2decision_past->variable.var_name) {
						if (p2decision_past->mode == CONFLICT_MODE) {
							var_table[p2decision_past->variable.var_name].value = VAL_UNASSIGNED;
							var_table[p2decision_past->variable.var_name].decision_clause = CLAUSE_UNASSIGNED;
							var_table[p2decision_past->variable.var_name].decision_level = LEVEL_UNASSIGNED;
							free(p2decision);
							free(p2decision_past);
							record_decided_decision.pop_back();
							record_decided_decision.pop_back();
							if (record_decided_decision.empty()) {
								end_solving = true;
								return;
							}
							break;
						}
					}
					undo_var(p2decision_past->variable.var_name);
					free(p2decision_past);
					record_decided_decision.pop_back();
				} else {
					break;
				}
			} else {
				break;
			}
		}
		p2decision = record_decided_decision.back();
		//TODO
		uint32_t target_level = p2decision->variable.decision_level;
		IS_FirstUIP_RETRY = true;
		vector<uint32_t>::iterator it;
		it = find(recorded_backtracking_level.begin(), recorded_backtracking_level.end(), p2decision->variable.decision_level);
		if (it != recorded_backtracking_level.end()) {
			//Element found in myvector
			IS_FirstUIP_RETRY = false;
		} else {
			//Element not found in myvector
#ifdef debug
			printf("ADD:%d\n", target_level);
#endif
			recorded_backtracking_level.push_back(target_level);
		}
		//remove all recorded level until target is the last
		for (uint32_t i = 0; i < recorded_backtracking_level.size(); i++) {
			if (target_level < recorded_backtracking_level[i]) {
#ifdef debug
				printf("ERASE:%d\n", recorded_backtracking_level[i]);
#endif
				recorded_backtracking_level.erase(recorded_backtracking_level.begin() + i);
				i--;
			}
		}
		sort(recorded_backtracking_level.begin(), recorded_backtracking_level.end());
#ifdef debug
		printf("TARGET LEVEL = %d\n", target_level);
		printf("===========================\n");
		printf("recorded LEVEL seq: ");
		for (uint32_t i = 0; i < recorded_backtracking_level.size(); i++) {
			printf("%d ", recorded_backtracking_level[i]);
		}
		printf("\n");
		printf("===========================\n");
#endif
		if (IS_FirstUIP_RETRY) {
			current_level = p2decision->variable.decision_level;
			add_decision_queue(p2decision->variable.var_name, p2decision->variable.value, p2decision->mode, p2decision->variable.decision_level, p2decision->variable.decision_clause);
			free(p2decision);
			record_decided_decision.pop_back();
			IS_FirstUIP_RETRY = false;
		} else {
			//assign inverse value to target var
			if (p2decision->mode == DECISION_MODE) { //first conflict
				if (p2decision->variable.value == VAL_1) {
					value = VAL_0;
				} else {
					value = VAL_1;
				}
				current_level = p2decision->variable.decision_level;
				add_decision_queue(p2decision->variable.var_name, value, CONFLICT_MODE, p2decision->variable.decision_level, p2decision->variable.decision_clause);
			} else if (p2decision->mode == CONFLICT_MODE) { //second conflict
				if (p2decision->variable.var_name == first_decision_var) {
					end_solving = true;
					return;
				} else {
					back_tracking_CONFLICT();
				}
			} else if (p2decision->mode == UNIQUE_MODE) { //unique conflict
				//undo until other mode
				undo_var(p2decision->variable.var_name);
				free(p2decision);
				record_decided_decision.pop_back();
				p2decision = record_decided_decision.back();
				while (p2decision->mode == UNIQUE_MODE) {
					undo_var(p2decision->variable.var_name);
					free(p2decision);
					record_decided_decision.pop_back();
					p2decision = record_decided_decision.back();
				}
				if (p2decision->mode == CONFLICT_MODE) {
					back_tracking_CONFLICT();
				} else if (p2decision->mode == DECISION_MODE) {
					if (p2decision->variable.value == VAL_1) {
						value = VAL_0;
					} else {
						value = VAL_1;
					}
					current_level = record_decided_decision.back()->variable.decision_level;
					add_decision_queue(record_decided_decision.back()->variable.var_name, value, CONFLICT_MODE, record_decided_decision.back()->variable.decision_level, record_decided_decision.back()->variable.decision_clause);
				} else {
					printf("ERROR in back_tracking to wrong mode\n");
					exit(EXIT_FAILURE);
				}
			} else { //FirstUIP this will never get into this situation
				printf("ERROR in back_tracking to no corresponding MODE\n");
				exit(EXIT_FAILURE);
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
	if (p2decision->variable.value == VAL_1) {
		need_new_decision_clause_list = &var_negative_watched_clause_table[p2decision->variable.var_name];
	} else if (p2decision->variable.value == VAL_0) {
		need_new_decision_clause_list = &var_postive_watched_clause_table[p2decision->variable.var_name];
	} else {
		fprintf(stderr, "This decision value is undecided yet!\n");
	}

	/*4 cases*/
	loop_size = (int)need_new_decision_clause_list->size();
	for (int i = 0; i < loop_size; i++) {
		current_clause = (*need_new_decision_clause_list)[i];
		the_other_watched_var = find_the_other_watched_var(p2decision->variable.var_name, current_clause);
		// CASE 1:
		if ((unwatched_unassigned_var = find_unwatched_unassigned_var(p2decision->variable.var_name, the_other_watched_var, current_clause))
		    != UNDECIDED_VAR_NAME) {
			//add this var be the new watched var in the clause
			idx = -1;
			new_watched_var = unwatched_unassigned_var;
			for (uint32_t j = 0; j < input_clause[current_clause].size(); j++) {
				if ((int)abs(input_clause[current_clause][j]) ==  new_watched_var) {
					idx = j;//the new_watched_var index in input_clause
					break;
				}
			}
			assert(idx != -1);
			if (input_clause[current_clause][idx] > 0) {
				var_postive_watched_clause_table[new_watched_var].push_back(current_clause);
			} else {
				var_negative_watched_clause_table[new_watched_var].push_back(current_clause);
			}
			update_VSIDS_counter(new_watched_var, VSIDS_UPDATE_ADD);
			//remove the old watched var from the clause
			need_new_decision_clause_list->erase(need_new_decision_clause_list->begin() + i);
			update_VSIDS_counter(p2decision->variable.var_name, VSIDS_UPDATE_DELETE);
			i--;//due to remove one clause,the idx need to remain same;
			loop_size = (uint32_t)need_new_decision_clause_list->size();//update loop size

		} else if (is_unit_clause(current_clause)) { //case 3
			//do nothing
			continue;
		} else if (var_table[the_other_watched_var].value == VAL_UNASSIGNED) { //case 2
			int value = VAL_UNASSIGNED;
			if (is_input_clause_var_postive(current_clause, the_other_watched_var)) {
				value = VAL_1;
			} else {
				value = VAL_0;
			}
			//TODO: fix the wrong assignment to already exist var
			if (var_table[the_other_watched_var].value != VAL_UNASSIGNED) {
				if (var_table[the_other_watched_var].value == value) {
					continue;
				} else {
					back_tracking(current_clause);
                    return;
				}
			} else {
				add_decision_queue(the_other_watched_var, value, UNIQUE_MODE, current_level, current_clause);
			}
		} else { //case 4(conflict)
			if (record_decided_decision.back()->mode == CONFLICT_MODE) { //second conflict
				back_tracking(current_clause);
				return;
			} else { //first conflict
				int current_value = record_decided_decision.back()->variable.value;
				int reverse_value;
				if (record_decided_decision.back()->mode == UNIQUE_MODE) {
					back_tracking(current_clause);
					return;
				}
				if (current_value == VAL_0) {
					reverse_value = VAL_1;
				} else {
					reverse_value = VAL_0;
				}
				add_decision_queue(record_decided_decision.back()->variable.var_name, reverse_value, CONFLICT_MODE, record_decided_decision.back()->variable.decision_level, record_decided_decision.back()->variable.decision_clause);
			}
			return;
		}
	}
}



static inline void print_result(void)
{
	for (uint32_t i = start_var_table_idx; i < end_var_table_idx; i++) {
		if (var_table[i].value == VAL_1) {
			printf("%d ", i);
		} else if (var_table[i].value == VAL_0) {
			printf("-%d ", i);
		} else { // default value for those don't care var
			printf("%d ", i);
		}
	}
}

static bool verify_result(void)
{
	bool result = false;
	bool clause_result = false;
	int loop_size  = (uint32_t)input_clause.size();

	for (int i = 0; i < loop_size; i++) {
		clause_result = false;
		for (uint32_t j = 0; j < input_clause[i].size(); j++) {
			if (var_table[abs(input_clause[i][j])].value == VAL_0) {
				if (input_clause[i][j] < 0) {
					clause_result = true;
				}
			} else if (var_table[abs(input_clause[i][j])].value == VAL_1) {
				if (input_clause[i][j] > 0) {
					clause_result = true;
				}
			} else { //unassigned
				//do nothing
			}
		}
		if (!clause_result) {
			return false;
		}
		input_clause.erase(input_clause.begin() + i);
		i--;
		loop_size = input_clause.size();
	}
	if (input_clause.empty()) {
		result = true;
	} else {
		result = false;
	}
	return result;
}

void solver(void)
{
	decision *p2decision;
	while (1) {
		if (decision_queue.empty()) {
			/*find a decision*/
			if (!make_decision()) { /*if no other decision could make*/
				if (!verify_result()) {
					printf("s UNSATISFIABLE\n");
					return;
				} else {
					printf("s SATISFIABLE\n");
					printf("v ");
					print_result();
					printf("0\n");
					return;
				}
			} else {
				//do nothing:find a decision
			}
		} else { //doing work based on decision_queue
			while (!decision_queue.empty()) {
				p2decision = decision_queue.front();
				assert(p2decision->variable.value != VAL_UNASSIGNED);
				decision_queue.erase(decision_queue.begin());//not actually destroy the first element,only the reference
				record_decided_decision.push_back(p2decision);
				var_table[p2decision->variable.var_name].value = p2decision->variable.value;
				var_table[p2decision->variable.var_name].decision_level = p2decision->variable.decision_level;
				var_table[p2decision->variable.var_name].decision_clause = p2decision->variable.decision_clause;
#ifdef debug
				if (p2decision->variable.value == VAL_0) {
					printf("VAR: -%d ", p2decision->variable.var_name);
				} else {
					printf("VAR: %d ", p2decision->variable.var_name);
				}
				int mode = p2decision->mode;
				switch (mode) {
				case UNIQUE_MODE:
					printf(" UNIQUE_MODE");
					break;
				case DECISION_MODE:
					printf(" DECISION_MODE");
					break;
				case CONFLICT_MODE:
					printf(" CONFLICT_MODE");
					break;
				case START_SYMBOL_MODE:
					printf(" START_SYMBOL_MODE");
					break;
				default:
					printf("MODE ERROR");
					exit(EXIT_FAILURE);
				}
				printf(" LEVEL: %d ", p2decision->variable.decision_level);
				printf(" CLAUSE: %d \n", p2decision->variable.decision_clause);
#endif
				update_two_watching_literal(p2decision);
			}
		}
	}
}

void preprocess_input(void)
{
	vector<int>::iterator p2var;
	vector<int> removed_list;
	for (uint32_t i = 0; i < input_clause.size(); i++) {
		removed_list.clear();
        //remove duplicate var in the same clause
		for (uint32_t j = 1; j < input_clause[i].size(); j++) {
			//first var never duplicate,start from second
			p2var = find(input_clause[i].begin(), input_clause[i].begin() + j, input_clause[i][j]);
			if (p2var != input_clause[i].begin() + j) { //find duplicate var
				removed_list.push_back(*p2var);
				input_clause[i].erase(p2var);
				j--;
			}
		}
		//if there is same var but different value in one clause:UNSAT
        for(uint32_t j = 1;j < input_clause[i].size();j++){
            for(uint32_t k = 0;k < j; k++){
                if( abs(input_clause[i][k])==abs(input_clause[i][j]) ){
                    if(input_clause[i][k] != input_clause[i][j]){
                        //UNSAT
                        end_solving = true;
                    }
                }
            }
        }
	}
}

int main(int argc, char *argv[])
{
	/*read cnf file*/
	int max_name;
	parse_DIMACS_CNF(input_clause, max_name, argv[1]);
	max_var_name = (uint32_t)max_name;
	/*remove duplicated same var more than one in same clause*/
	preprocess_input();
	/*build var_table for management*/
	build_var_table();
	/*traverse all clause to initialize the initial two watched var for each and unique decision*/
	init_solver();
	/*main algorithm*/
	solver();

	/*clean up*/
	while (!decision_queue.empty()) {
		free(decision_queue.back());
		decision_queue.pop_back();
	}
	while (!record_decided_decision.empty()) {
		free(record_decided_decision.back());
		record_decided_decision.pop_back();
	}
	free(var_table);
	return 0;
}
