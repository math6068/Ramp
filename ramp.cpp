#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include <string.h>
#include <climits>
#include <ctime>

#include "myHeap.h"
#include "myBijection.h"
using namespace std;

typedef long long LL;

//#define debug_mode

#define ans_op_mode

#define reset_mode

#define dec_hard_weight_mode

#define bad_var_cscc_mode

#define score_make_mode

//#define unlock_all_neighbor_mode
//#define unlock_add_to_1_mode
//#define unlock_mis_to_0_mode

//#define age_init_0
#define age_init_i

double second1 = 1000000.0;

int time_limit = 295;
int print_speed = 50000;
double time_convergence = 3.0;
int answer_writed = 0;

int flag_weighted = 0;

#ifdef bad_var_cscc_mode
Bijection *ptr_to_bad_var;
int greedy = 1;
#endif

//cutoff
LL  max_flips = 20000000000000ll;
LL	flip_bound = 0;
LL 	step = 1;
int trie = 1;

#ifdef last_second_flip_time_mode
LL *last_second_flip_time;
#endif

#ifdef dec_hard_weight_mode
LL last_achieved_weight_unsat;
#endif

// Define a data structure for a literal in the SAT problem.
struct lit 
{
    int clause_num;		//clause num, begin with 0
    int var_num;		//variable num, begin with 1
    int sense;			//is 1 for true literals, 0 for false literals.
};

/*parameters of the instance*/
int     var_n;		//var index from 1 to var_n
int     clause_n;	//clause index from 0 to clause_n-1

/* literal arrays */				
lit**	var_lit;//[MAX_VARS];				//var_lit[i][j] means the j'th literal of var i.
int*	var_lit_count;//[MAX_VARS];        //amount of literals of each var
lit**	clause_lit;//[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
int*		clause_lit_count;//[MAX_CLAUSES]; 	// amount of literals in each clause			
			
/* Information about the variables. */
LL*     score;//[MAX_VARS];				
LL*		last_flip_time;//[MAX_VARS];
//int*		conf_change;//[MAX_VARS];
int**	var_neighbor;//[MAX_VARS];
int*		var_neighbor_count;//[MAX_VARS];

/* Information about the clauses */	
LL weight_unsat_best;
double time_best = 0;
LL step_best = 0;
int trie_best = 0;
LL weight_unsat;
LL weight_hard;
LL*     weight;//[MAX_CLAUSES];		
int*    sat_n;//[MAX_CLAUSES];			
int*	sat_var;//[MAX_CLAUSES];

//unsat clauses stack
Bijection *ptr_to_c0;

#ifdef score_make_mode
int*	score_make;//[MAX_VARS];		//a varible appears in how many unsat clauses
#endif

HeapGreedyCand *pHeapGreedyCand;
bool heap_worse(const int &a, const int &b)
// if a is worse than b, return 1, otherwise return 0
{
	if(score[a] < score[b] || score[a] == score[b] && last_flip_time[a] > last_flip_time[b])
		return 1;
	else return 0;
}
#ifdef ans_op_mode
Bijection *ptr_to_ans;
#endif
void Write_answer();
/* Information about solution */
int* value;//[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables
int* value_best;//[MAX_VARS];

void free_memory();
int build_instance(char *filename);
void build_neighbor_relation();

void free_memory()
{
	int i;
	for(i = 0; i < clause_n; i++) 
	{
		delete[] clause_lit[i];
	}
	
	for(i = 1; i <= var_n; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}
		
	//zz
	delete[] score_make;
	delete[] var_lit;
	delete[] var_lit_count;
	delete[] clause_lit;
	delete[] clause_lit_count;
	delete[] score;
	delete[] last_flip_time;
#ifdef last_second_flip_time_mode
	delete[] last_second_flip_time;
#endif
	//delete[] conf_change;
	delete[] var_neighbor;
	delete[] var_neighbor_count;
	delete[] weight;
	delete[] sat_n;
	delete[] sat_var;

	delete ptr_to_c0;
	delete pHeapGreedyCand;
	delete ptr_to_ans;

#ifdef bad_var_cscc_mode
	delete ptr_to_bad_var;
#endif

	delete[] value;
	delete[] value_best;
}

/*
 * Read the instance
 */
int build_instance(char *filename)
{
	char    line[1024];
	char    tempstr1[10];
	char    tempstr2[10];
	int     cur_lit;
	int     i, j;
	int		v, c;//var, clause
	
	ifstream infile(filename);
	if(infile == NULL)
		return 0;

	/*** build problem data structures of the instance ***/
	do{
	infile.getline(line, 1024);
	}while(line[0] != 'p');

	weight_hard = 0;
	
	int line_n=strlen(line);
	line[line_n++] = ' ';
	line[line_n++] = '0';
	line[line_n] = 0;
	
	//cout<<line<<endl;
	
	sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &var_n, &clause_n, &weight_hard);
		
	time_limit -= var_n / print_speed;
	
	//cout<<var_n<<' '<<clause_n<<' '<<weight_hard<<endl;
	
	//zz
	score_make = new int[var_n+2];
	var_lit = new lit*[var_n+2];
	var_lit_count = new int[var_n+2];
	clause_lit = new lit*[clause_n+2];
	clause_lit_count = new int[clause_n+2];
	score = new LL[var_n+2];
	last_flip_time = new LL[var_n+2];
#ifdef last_second_flip_time_mode
	last_second_flip_time = new LL[var_n+2];
#endif
	//conf_change = new int[var_n+2];
	var_neighbor = new int*[var_n+2];
	var_neighbor_count = new int[var_n+2];
	weight = new LL[clause_n+2];
	sat_n = new int[clause_n+2];
	sat_var = new int[clause_n+2];

	ptr_to_c0 = new Bijection(clause_n);
	pHeapGreedyCand = new HeapGreedyCand(heap_worse, var_n);
	ptr_to_ans = new Bijection(var_n);

#ifdef bad_var_cscc_mode
	ptr_to_bad_var = new Bijection(var_n);
#endif

	value = new int[var_n+2];
	value_best = new int[var_n+2];

	int *temp_lit = new int[var_n+2];
	
	//cout<<weight_hard<<endl;
	
	if(strcmp(tempstr2, "wcnf") == 0)
		flag_weighted = 1;

	for (c = 0; c < clause_n; c++) 
		clause_lit_count[c] = 0;
	for (v = 1; v <= var_n; ++v)
		var_lit_count[v] = 0;
		
	//Now, read the clauses, one at a time.
	for(c = 0; c < clause_n; c++) 
	{
		if(flag_weighted)
			infile >> weight[c];
		else
			weight[c] = 1;
		
		infile >> cur_lit;

		while (cur_lit != 0) { 
			temp_lit[clause_lit_count[c]] = cur_lit;
			clause_lit_count[c]++;
		
			infile>>cur_lit;
		}
		
		clause_lit[c] = new lit[clause_lit_count[c] + 1];
		
		for(i = 0; i < clause_lit_count[c]; ++i)
		{
			clause_lit[c][i].clause_num = c;
			clause_lit[c][i].var_num = abs(temp_lit[i]);
			if (temp_lit[i] > 0) clause_lit[c][i].sense = 1;
				else clause_lit[c][i].sense = 0;
			
			var_lit_count[clause_lit[c][i].var_num]++;
		}
		clause_lit[c][i].var_num = 0; //end flag
		clause_lit[c][i].clause_num = -1;//end flag
	}
	delete[] temp_lit;
	infile.close();
	
	//creat var literal arrays
	for(v = 1; v <= var_n; ++v)
	{
		var_lit[v] = new lit[var_lit_count[v] + 1];
		var_lit_count[v] = 0;	//reset to 0, for build up the array
	}
	//scan all clauses to build up var literal arrays
	for (c = 0; c < clause_n; ++c) 
	{
		for(i = 0; i < clause_lit_count[c]; ++i)
		{
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];
		}
	}
	for (v = 1; v <= var_n; ++v) //set boundary
		var_lit[v][var_lit_count[v]].clause_num = -1;

	build_neighbor_relation();

	return 1;
}

void build_neighbor_relation()
{
	int	i, j, count;
	int v, c;

	int *neighbor_flap_use = new int[var_n + 2];
	int neighbor_flap_use_n = 0;
	int*neighbor_flag = new int[var_n + 2];	

	memset(neighbor_flag, 0, sizeof(int) * (var_n + 1));
	
	for(v = 1; v <= var_n; ++v)
	{
		var_neighbor_count[v] = 0;		
		neighbor_flag[v] = 1;
		neighbor_flap_use[neighbor_flap_use_n++] = v;//v itself entered		
		
		for(i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for(j = 0; j < clause_lit_count[c]; ++j)
			{
				if(neighbor_flag[clause_lit[c][j].var_num] == 0)
				{
					var_neighbor_count[v]++;
					neighbor_flag[clause_lit[c][j].var_num] = 1;
					neighbor_flap_use[neighbor_flap_use_n++] = clause_lit[c][j].var_num;
				}
			}
		}

		var_neighbor[v] = new int[var_neighbor_count[v] + 1];

		count = 0;
		for(i = 1; i < neighbor_flap_use_n; ++i)
		{
			var_neighbor[v][count] = neighbor_flap_use[i];
			count++;
		}
		var_neighbor[v][count] = 0;				
		
		for(i = 0; i < neighbor_flap_use_n; ++i)
			neighbor_flag[neighbor_flap_use[i]] = 0;
		neighbor_flap_use_n = 0;
	}
	
	delete[] neighbor_flag; neighbor_flag = NULL;
	delete[] neighbor_flap_use; neighbor_flap_use = NULL;
}

void print_solution()
{
     int i;
     cout << "v ";
     for (i = 1; i <= var_n; i++) {
         if(value[i] == 0) cout << "-";
         cout << i;
         if(i % 10 == 0) cout << endl << "v ";
         else cout << ' ';
     }
     cout << "0" << endl;
}


int verify_sol()
//only check satisfiability, not for maxsat
{
	int c, j; 
	int flag;
	
	for (c = 0; c < clause_n; ++c) 
	{
		flag = 0;
		for(j = 0; j < clause_lit_count[c]; ++j)
			if(value[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}

		if(flag == 0){//output the clause unsatisfied by the solution
			cout << "clause " << c << " is not satisfied" << endl;
			
			for(j = 0; j < clause_lit_count[c]; ++j)
			{
				if(clause_lit[c][j].sense == 0) cout << "-";
				cout << clause_lit[c][j].var_num << " ";
			}
			cout << endl;
			
			for(j = 0; j < clause_lit_count[c]; ++j)
				cout << value[clause_lit[c][j].var_num] << " ";
			cout << endl;

			return 0;
		}
	}
	return 1;
}

int init_try = 1;

#ifdef ans_op_mode
void Ans_update(int flipvar)
{
	if(!ptr_to_ans->element_in(flipvar))
	{
		ptr_to_ans->insert_element(flipvar);
	}
	else
	{
		ptr_to_ans->delete_element(flipvar);
	}
}
#endif

void init()
{
	int v, c;
	int	i, j;
	
#ifdef bad_var_cscc_mode	
	ptr_to_bad_var->clear();
#endif	
	ptr_to_c0->clear();

	if(init_try)
	{	
		for(v = 1; v <= var_n; v++)
		{ 
			value[v] = 0;
			value_best[v] = 0;
		}
	}
	//init solution
	for(v = 1; v <= var_n; v++) 
	{
		if(rand() % 2) 
		{
			value[v] = 1 - value[v];			
			if(init_try)
				value_best[v] = value[v];			
#ifdef ans_op_mode
			if(!init_try)
			{
				Ans_update(v);
			}
#endif
		}				
#ifdef age_init_0
		last_flip_time[v] = 0;
	#ifdef last_second_flip_time_mode
		last_second_flip_time[v] = 0;
	#endif
#endif		

#ifdef age_init_i
		last_flip_time[v] = v - 1 - var_n;
	#ifdef last_second_flip_time_mode
		last_second_flip_time[v] = v - 1 - var_n;
	#endif
#endif
		//conf_change[v] = 1;
#ifdef score_make_mode		
		score_make[v] = 0;
#endif		
	}
#ifdef debug_mode
print_solution();
#endif
	weight_unsat = 0;
	/* figure out sat_n, and init c0 */
	for(c = 0; c < clause_n; ++c) 
	{
		sat_n[c] = 0;
		
		for(j = 0; j < clause_lit_count[c]; ++j)
		{
			if(value[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				v = clause_lit[c][j].var_num;
				sat_n[c]++;	
				if(sat_n[c] == 1)		
					sat_var[c] = v;				
			}
		}

		if(sat_n[c] == 0) 
		{
			ptr_to_c0->insert_element(c);
	
#ifdef score_make_mode	
			for(lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
			{	
				score_make[v]++;
			}
#endif
			weight_unsat += weight[c];
		}
	}	
/*
	for(c = 0; c < clause_n; c++)
		if(sat_n[c] == 0)
		{
			weight_unsat += weight[c];
		}
*/	
	if(init_try)
	{
		if(weight_hard == 0 || weight_unsat < weight_hard)
		{
			weight_unsat_best = weight_unsat;
		}
		else
		{
			weight_unsat_best = LLONG_MAX;
		}
	}

	/*figure out var score*/
	int lit_count;
	for (v = 1; v <= var_n; v++) 
	{
		score[v] = 0;

		lit_count = var_lit_count[v];
		
		for(i = 0; i < lit_count; ++i)
		{
			c = var_lit[v][i].clause_num;
			if(sat_n[c] == 0) score[v] += weight[c];
			else if(sat_n[c] == 1 && var_lit[v][i].sense == value[v]) score[v] -= weight[c];			
		}
	}

#ifdef debug_mode
	#if 0
	cout << "value:" << endl;
	for(v = 1; v <= var_n; v++)
	{
		if(value[v] == 0) cout << "-";
		cout << v << "\t";
	}
	cout << endl;
	cout << "score:" << endl;
	for(v = 1; v <= var_n; v++)
		cout << score[v] << "\t";
	cout << endl;
	cout << "score_make:" << endl;
	for(v = 1; v <= var_n; v++)
		cout << score_make[v] << "\t";
	cout << endl;
	#endif
#endif
			pHeapGreedyCand->init(score_make, var_n);
#ifdef debug_mode
			if(!pHeapGreedyCand->check())
			{
				cout << "init score_make heap failure" << endl;
				exit(1);
			}
#endif
	//setting for the virtual var 0
	last_flip_time[0] = 0;

	init_try = 0;	
}

///f3
void flip_3SAT(int flipvar)
{
	value[flipvar] = 1 - value[flipvar];
	
	int i, j;
	int v, c;
	lit* clause_c;
#ifdef ans_op_mode
	Ans_update(flipvar);
#endif	
	int org_flipvar_score = score[flipvar];
#ifdef bad_var_cscc_mode
	// flipping an increasing variable in greedy mode
	if(greedy && org_flipvar_score < 0)
	{
		if(!ptr_to_bad_var->element_in(flipvar))
			ptr_to_bad_var->insert_element(flipvar);
	}
#endif	
	//update related clauses and neighbor vars
	for(lit *q = var_lit[flipvar]; (c = q->clause_num) >= 0; q++)
	{
		clause_c = clause_lit[c];

		if(value[flipvar] == q->sense)
		{
			++sat_n[c];
			
			if(sat_n[c] == 2) //sat_n from 1 to 2
			{		
				score[sat_var[c]] += weight[c];
				if(pHeapGreedyCand->element_in(sat_var[c]))
					pHeapGreedyCand->heap_up(pHeapGreedyCand->index_of(sat_var[c]));				
			}
			else if(sat_n[c] == 1) // sat_n from 0 to 1
			{
					sat_var[c] = flipvar;//record the only true lit's var				
					for(lit *p = clause_c; (v = p->var_num) != 0; p++) 
					{
						score_make[v]--;					
						if(v != flipvar)
						{
							score[v] -= weight[c];
							if(pHeapGreedyCand->element_in(v))
								pHeapGreedyCand->heap_down(pHeapGreedyCand->index_of(v));						
#ifdef bad_var_cscc_mode
							// cscc leads v from the bad var set
							if(ptr_to_bad_var->element_in(v))
							{								
								ptr_to_bad_var->delete_element(v);
							}
#endif		
	#ifdef unlock_add_to_1_mode
							conf_change[v]++;
	#endif		
						}							
					}
				ptr_to_c0->delete_element(c);
				weight_unsat -= weight[c];
			}
		}
		else // value[flipvar] != cur_lit.sense
		{
			--sat_n[c];
			if(sat_n[c] == 1) //sat_n from 2 to 1
			{	
				for(lit* p = clause_c; (v = p->var_num) != 0; p++) 
				{
					if(p->sense == value[v])
					{
						score[v] -= weight[c];
						sat_var[c] = v;						
						if(pHeapGreedyCand->element_in(v))
							pHeapGreedyCand->heap_down(pHeapGreedyCand->index_of(v));							
						break;
					}
				}
			}
			else if(sat_n[c] == 0) //sat_n from 1 to 0
			{
				for(lit *p = clause_c; (v = p->var_num) != 0; p++) 
				{
					score_make[v]++;										
					if(v != flipvar)
					{
						score[v] += weight[c];
						if(pHeapGreedyCand->element_in(v))
							pHeapGreedyCand->heap_up(pHeapGreedyCand->index_of(v));							
		#ifdef unlock_mis_to_0_mode
						conf_change[v]++;
		#endif
#ifdef bad_var_cscc_mode
						// cscc leads v from the bad var set
						if(ptr_to_bad_var->element_in(v))
						{								
							ptr_to_bad_var->delete_element(v);
						}
#endif	
					}
				}	
				ptr_to_c0->insert_element(c);				
				weight_unsat += weight[c];
			}			
		}//end else
	}
	score[flipvar] = -org_flipvar_score;	
	//conf_change[flipvar] = 0;	
#ifdef last_second_flip_time_mode
		last_second_flip_time[flipvar]=last_flip_time[flipvar];
#endif
		last_flip_time[flipvar] = step;

#ifdef debug_mode
cout << "flipvar: " << flipvar << endl;
cout << "location of flipvar " << flipvar << " in heap: " << pHeapGreedyCand->index_of(flipvar) << endl;
#endif

	if(pHeapGreedyCand->element_in(flipvar))	
	{
		if(score_make[flipvar] <= 0)
		{
			pHeapGreedyCand->heap_del(flipvar);
#ifdef debug_mode
if(!pHeapGreedyCand->check_map())
{
	cout << "a. heap error at step " << step << endl;
	exit(1);
}
#endif	
		}	
	#ifdef bad_var_cscc_mode
		else if(ptr_to_bad_var->element_in(flipvar))
		{
#ifdef debug_mode
//cout << "bad var deleted..............................." << endl;
#endif			
			pHeapGreedyCand->heap_del(flipvar);
#ifdef debug_mode
if(!pHeapGreedyCand->check_map())
{
	cout << "b. heap error at step " << step << endl;
	exit(1);
}
#endif	
		}
	#endif
		else 
		{
#ifdef debug_mode
if(!pHeapGreedyCand->check_map())
{
	cout << "c. heap error at step " << step << endl;
	exit(1);
}
#endif	
			if(org_flipvar_score < 0)
			{
#ifdef debug_mode
cout << 1 << endl;
#endif
				pHeapGreedyCand->heap_up(pHeapGreedyCand->index_of(flipvar));
			}
			else 
			{
#ifdef debug_mode
cout << 2 << endl;
#endif
#ifdef debug_mode
if(!pHeapGreedyCand->check_map())
{
	cout << "d. heap error at step " << step << endl;
	exit(1);
}
#endif
				pHeapGreedyCand->heap_down(pHeapGreedyCand->index_of(flipvar));
#ifdef debug_mode
if(!pHeapGreedyCand->check_map())
{
	cout << "e. heap error at step " << step << endl;
	exit(1);
}
#endif
			}
	
		}
#ifdef debug_mode
if(!pHeapGreedyCand->check())
{
	cout << "1. heap error at step " << step << endl;
	exit(1);
}
#endif	
	}
	else
	{
	#ifdef bad_var_cscc_mode
		if(ptr_to_bad_var->element_in(flipvar))
		{
#ifdef debug_mode
cout << "bad var not inserted..............................." << endl;
getchar();
#endif
		}
		else
	#endif
		if(score_make[flipvar] > 0)
		{
			pHeapGreedyCand->heap_add(flipvar);
		}
#ifdef debug_mode
if(!pHeapGreedyCand->check())
{
	cout << "2. heap error at step " << step << endl;
	exit(1);
}
#endif	
	}
	//update all flipvar's neighbor's conf_change to be 1, add goodvar
	int *p;
	for(p = var_neighbor[flipvar]; (v = *p) != 0; p++)
	{
#ifdef unlock_all_neighbor_mode
		//conf_change[v]++;
#endif					
		if(pHeapGreedyCand->element_in(v))
		{
			if(score_make[v] <= 0)// || conf_change[v]<=0)
			{
#ifdef debug_mode
//cout << "about to delete " << v << " from heap" << endl;
#endif
				pHeapGreedyCand->heap_del(v);
			}
#ifdef bad_var_cscc_mode
			else if(ptr_to_bad_var->element_in(v))
			{
#ifdef debug_mode
//cout << "bad var deleted..............................." << endl;
#endif
				pHeapGreedyCand->heap_del(v);
			}
#endif
#ifdef debug_mode
if(!pHeapGreedyCand->check())
{
	cout << "3. heap error at step " << step << endl;
	exit(1);
}
#endif	
		}
		else
		{	
			if(score_make[v] > 0)// && conf_change[v]>0)
#ifdef bad_var_cscc_mode
			if(ptr_to_bad_var->element_in(v))
			{
#ifdef debug_mode
cout << "bad var not inserted..............................." << endl;
getchar();
#endif
			}
			else
#endif
			{
				pHeapGreedyCand->heap_add(v);
			}
#ifdef debug_mode
if(!pHeapGreedyCand->check())
{
	cout << "4. heap error at step " << step << endl;
	exit(1);
}
#endif		
		}		
	}	
}

void (* flip)(int);

int p1 = 6000;
///p3
int pick_var_3SAT()
{
	int         i, k;
	int 		c, v;
	int         ret = 0;
	lit			*clause_c;

	if(rand() % 10000 < p1 && pHeapGreedyCand->exists_elements())
	{
		ret = pHeapGreedyCand->top_element();
#ifdef bad_var_cscc_mode
		greedy = 1;
#endif
#ifdef debug_mode
cout << "in pick_var_3SAT, having greedily picked " << ret << endl;
#endif	
		return ret;
	}

	{
		c = ptr_to_c0->at(rand() % ptr_to_c0->size() + 1);
		v = clause_lit[c][rand() % clause_lit_count[c]].var_num;

#ifdef debug_mode
cout << "in pick_var_3SAT, having randomly picked " << v << endl;
#endif	
#ifdef bad_var_cscc_mode
		// only consider those increasing variables flipped in the greedy mode as bad vars
		if(ptr_to_bad_var->element_in(v))
		{								
			ptr_to_bad_var->delete_element(v);
		}
		//if(!ptr_to_bad_var->element_in(v));	
		greedy = 0;
#endif
		return v;
	}
}

int (* pick_var) ();


//set functions in the algorithm
void set_functions()
{	
	flip = flip_3SAT;
	pick_var = pick_var_3SAT;
}

#ifdef dec_hard_weight_mode
// still need further considerations
void decrease_hard_weight()
{
	int diff = last_achieved_weight_unsat - weight_unsat_best;

	for(int c = 0; c < clause_n; c++)
	{
		if(weight[c] == last_achieved_weight_unsat)// for each hard clause
		{
			weight[c] = weight_unsat_best;// decrease its weight to the current best objective value
			if(sat_n[c] == 1)
			{
				int sat_var_in_c = sat_var[c];
				score[sat_var_in_c] += diff;
				if(pHeapGreedyCand->element_in(sat_var_in_c))
				{
					pHeapGreedyCand->heap_up(pHeapGreedyCand->index_of(sat_var_in_c));
				}
			}
		}
	}
	last_achieved_weight_unsat = weight_unsat_best;// update the achieved target
#ifdef debug_mode
cout << "last_achieved_weight_unsat updated to be " << last_achieved_weight_unsat << endl;
#endif
}
#endif

void local_search(LL flip_bound)
{
	int flipvar;
	int i;
   
	while(step <= flip_bound)
	{
		flipvar = pick_var();

		flip(flipvar);
#ifdef debug_mode
if(!pHeapGreedyCand->check())
{
	cout << "heap error at step " << step << endl;
	exit(1);
}
#endif	
		if(weight_unsat_best > weight_unsat && (!weight_hard || weight_unsat < weight_hard))
		{			
			weight_unsat_best = weight_unsat;
				
			//answer_writed=0;
			time_best = clock() / 1000000.0;
			step_best = step;
			trie_best = trie;

cout << "o " << weight_unsat_best << endl;
			//cout << "c time " << time_best << endl;
		
			answer_writed = 0;

#ifdef ans_op_mode
			ptr_to_ans->clear();
#endif
#ifdef dec_hard_weight_mode
			if(weight_hard)
				decrease_hard_weight();
#endif
		}

/*			
		if(!answer_writed || clock() / 1000000.0 > time_best * time_convergence)
		{
			Write_answer();
			answer_writed = 1;
		}
*/
		//find a solution
		if(!ptr_to_c0->size()) 
			{weight_unsat_best = 0; return;}

		//update the output answer iteratively with double cutoff
		if(!(step % 10000))
		{
			if(clock() > time_limit * 1000000.0) return;
		}	

#ifdef debug_mode
/*		
		if(!(step % 100000))
				{
					int z=(int)(clock() / 1000000.0);
					{
						printf("c c ");
						printf("ft=%10.lld, ",step);
						printf("t=%4.d, ",z);
						printf("t=%5.2lf, ",clock()/1000000.0);
						printf("fs=%7.d, ",int(step/(clock()/1000000.0)));
						printf("Dw=%8.lld, ",weight_unsat_best);
						printf("Wu=%8.lld, ",weight_unsat);
						//printf("c0_n=%6.d, ",c0_n);
						printf("fv=%6.d, ",flipvar);				
						printf("cutoff=%d, ",time_limit);
						printf("\n");
						fflush(stdout);
					}
				}
*/
	//	getchar();
#endif	
		step++;
	}
}


void Write_answer()//output the best answer
{
	int v;
	printf("v");

	for(v = 1; v <= var_n; v++)
	{
		putchar(' ');
		if(!value_best[v]) putchar('-');
		printf("%d", v);
	}	
	puts("");
}

int Check()
{
	LL s = 0;
	int c, flag, j;
	
	for (c = 0; c < clause_n; ++c) 
	{
		flag = 0;
		for(j = 0; j < clause_lit_count[c]; ++j)
			if (value_best[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}

		if(flag == 0){//
			s += weight[c];			
		}
	}
	
	if(s != weight_unsat_best)
	{
		return 0;
	}
	return 1;
}

int main(int argc, char* argv[])
{
	int seed, i;
     
	struct tms start, stop;
	times(&start);

	if(build_instance(argv[1]) == 0)
	{
		cout << "Invalid filename: " << argv[1] << endl;
		return -1;
	}	
    
	sscanf(argv[2], "%d", &seed);
    srand(seed);

	//srand(time(NULL));
    
    sscanf(argv[3], "%d", &time_limit);    
    
	set_functions();
	
#ifdef reset_mode	
	if(var_n > 100000)
		max_flips = 20000000000000ll;
	else
		max_flips = 20 * var_n;
#else
		max_flips = 20000000000000ll;
#endif
	step = 1;
	trie = 1;
#ifdef debug_mode
cout << "trie: " << trie << endl;
cout << "step: " << step << endl;
#endif
	while(1) 
	{
		init();	 

	 	flip_bound += max_flips;

		local_search(flip_bound);

		if(clock() > time_limit * 1000000.0)
		{	
			break;
		}

		if(!ptr_to_c0->size()) break;
		 
		max_flips <<= 2;

		trie++;
#ifdef debug_mode
cout << "trie: " << trie << endl;
cout << "step: " << step << endl;
#endif
	}
#ifdef debug_mode
cout << "at the end of the run, step: " << step << endl;
#endif
	times(&stop);
	double comp_time = double(stop.tms_utime - start.tms_utime + stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

LL total_flip_time;

#ifdef ans_op_mode
{
	int v;
	for(v = 1; v <= var_n; v++)
	{
		if(ptr_to_ans->element_in(v))
			value_best[v] = 1 - value[v];
		else			
			value_best[v] = value[v];
	}
}
#endif	
	if(!ptr_to_c0->size())
	{
		if(verify_sol() == 1)
		{
		//	print_solution();
			//printf("o %lld\n", weight_unsat_best);
			cout << "s OPTIMUM FOUND" << endl;
cout << "c solveTime " << time_best << endl;
cout << "c solveStep " << step << endl;
			//cout<<"c solveTime "<<comp_time<<endl;
            //cout << "c solveTrie " << trie << endl;
            //printf("c total_flip_time %lld\n", step);
			//cout << "c totalTrie " << trie << endl;
		//printf("c time %lf\n", double(clock())/1000000.0);
printf("c flip/ms %.2lf\n", double(step) / ((double)(clock())/1000000.0) / 1000.0);
		//total_flip_time=(step+2000000000ll*tryi) ;
			
			if(!answer_writed)
			{
				//printf("o %lld\n",weight_unsat_best);
				//printf("c time %lf\n",double(clock())/1000000.0);
				answer_writed = 1;
				//Write_answer();
			}
			
		//	Write_answer();
        }
        else 
		{
			cout << "s UNKNOWN" << endl;
			cout << "c Sorry, something is wrong."<<endl;
		}
    }
    else
    {
    	//printf("c total_flip_time %lld\n", step);
		//printf("c time %lf\n", double(clock())/1000000.0);	
		if(!weight_hard || weight_unsat_best < weight_hard)
		{
			if(Check())
			{
//cout << "o " << weight_unsat_best << endl;
				cout << "s UNKNOWN" << endl;
cout << "c solveTime " << time_best << endl;
cout << "c searchStep " << step_best << endl;
printf("c flip/ms %.2lf\n", (step) / ((double)(clock())/1000000.0) / 1000.0);    	  	
				if(!answer_writed)
				{

				//printf("o %lld\n",weight_unsat_best);

				//cout << "c solveTime " << time_best << endl;
				//cout << "c solveTrie " << trie_best << endl;
				//printf("c total_flip_time %lld\n", step);
				//cout << "c totalTries " << trie << endl;
				//printf("c time %lf\n",double(clock())/1000000.0);
				answer_writed = 1;
				//Write_answer();
				}			
			
    	  	

		//	Write_answer();
    		}
    		else
			{
				puts("s UNKNOWN");
    			puts("c Sorry, something is wrong.");
			}
		}
		else
		{
			cout << "s UNKNOWN" << endl;
			puts("c failure");
		}
	}    		
	
	//printf("c time %lf\n",double(clock())/1000000.0);
    	  	 
    free_memory();

    return 0;
}
