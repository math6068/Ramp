#ifndef _MY_HEAP_H
#define _MY_HEAP_H

#include <iostream>

using namespace std;

//#define debug_mode

class HeapGreedyCand
{
private:
	int* greedy_cand;
	int* index_in_greedy_cand;
	int	 greedy_cand_size;
	int	 greedy_cand_capacity;
	bool (*heap_worse)(const int &, const int &);

void clear()
{
	memset(greedy_cand, 0, sizeof(int) * greedy_cand_capacity);
	memset(index_in_greedy_cand, 0, sizeof(int) * greedy_cand_capacity);
	greedy_cand_size = 0;
}

public:

HeapGreedyCand(bool (*h_worse)(const int &, const int &), int sz)
{
	heap_worse = h_worse;
	greedy_cand_capacity = sz;
	greedy_cand = new int[greedy_cand_capacity];
	index_in_greedy_cand = new int[greedy_cand_capacity];
	memset(greedy_cand, 0, sizeof(int) * greedy_cand_capacity);
	memset(index_in_greedy_cand, 0, sizeof(int) * greedy_cand_capacity);
	greedy_cand_size = 0;
}

~HeapGreedyCand()
{
	greedy_cand_capacity = 0;
	delete[] greedy_cand;
	delete[] index_in_greedy_cand;
	greedy_cand_size = 0;
}

int top_element()
{
#ifdef debug_mode
if(greedy_cand_size <= 0)
{
	cout << "no elements in the heap, failure in obtaining the top element" << endl;
	exit(1);
}
#endif
	return greedy_cand[1];
}
int index_of(int name)
{
#ifdef debug_mode
if(index_in_greedy_cand[name] < 0 || index_in_greedy_cand[name] > greedy_cand_size)
{
	cout << "invalid index of var " << name << endl;
	cout << "the index is " << index_in_greedy_cand[name] << endl;
	exit(1);
}
#endif
	return index_in_greedy_cand[name];
}

void heap_up(int p)
//used when p may possibly be better than its parent
//push up the item pointed by p to the proper location
//if pushing up operations are not needed, it can return immediately without doing anything
{
#ifdef debug_mode
	if(p <= 0 || p > greedy_cand_size)
	{
		cout << "heap_up: input pointer error" << endl;
		exit(1);
	}
	if(!check_map())
	{
		cout << "mapping error" << endl;
		exit(1);
	}
#endif
	int q = p >> 1;// q is the parent node, p is one of the child node
	int a = greedy_cand[p];// to be placed in an upper location
	int z = greedy_cand[q];// 'z' is above 'a'
	while(q)// still a location in the heap
	{
		if(heap_worse(z, a))// 'z' is worse than 'a'
		{
			// push down 'z'
			greedy_cand[p] = z;
			index_in_greedy_cand[z] = p;
		}
		else
			break;
		// move 'p' and 'q' up to point to upper locations
		p = q;
		q = p >> 1;
		// obtain a new item for next comparisons
		z = greedy_cand[q];
	}
	// find the proper location for 'a'
	greedy_cand[p] = a;
	index_in_greedy_cand[a] = p;

#ifdef debug_mode
if(!check())
{
	cout << "heap_up: check error" << endl;
	exit(1);
}
#endif
}

void heap_down(int p)
//used when p may possibly be worse than either child
//push down the item pointed by p the the proper location
//if pushing down operations are not needed, it can return immediately without doing anything
{
#ifdef debug_mode
	if(p <= 0 || p > greedy_cand_size)
	{
		cout << "heap_down: input pointer error" << endl;
		exit(1);
	}
	if(!check_map())
	{
		cout << "mapping error" << endl;
		exit(1);
	}
#endif

	int q = p << 1;// p is the parent node, q is one of the child nodes 
	int a = greedy_cand[p];// parent item
	int x = greedy_cand[q];// left child
	int y = greedy_cand[q+1];// right child
	
	while(q <= greedy_cand_size)// q is a location in the heap
	{
		if(q < greedy_cand_size && heap_worse(x, y))// left child is worse, so only the right child can possibly be pushed up
		{
			if(heap_worse(a, y))// the right child is better than its parent
			{
				// push up 'y'
				greedy_cand[p] = y;
				index_in_greedy_cand[y] = p;
			}
			else
				break;
			// move 'p' and 'q' to point to lower locations
			p = q + 1;
			q = p << 1;		
			// obtain items for next comparisons
			x = greedy_cand[q];
			y = greedy_cand[q+1];
		}		
		else
		{
			if(heap_worse(a, x))// the right child is worse
			{
				// push up 'x'
				greedy_cand[p] = x;
				index_in_greedy_cand[x] = p;
			}
			else
				break;
			// move 'p' and 'q' to point to lower locations
			p = q;
			q = p << 1;	
			// obtain items for next comparisons	
			x = greedy_cand[q];
			y = greedy_cand[q+1];
		}
	}
	greedy_cand[p] = a;
	index_in_greedy_cand[a] = p;
}

void heap_del(int name)
{
//	printf("(((((((((((((((( heap_del %d %d\n", name, heap_vc[1]);
#ifdef debug_mode
	if(index_in_greedy_cand[name] <= 0 || index_in_greedy_cand[name] > greedy_cand_size)
	{
		cout << "heap_del: input pointer error" << endl;
		exit(1);
	}
#endif

	if(greedy_cand_size == index_in_greedy_cand[name])// when deleting the end element
	{
		greedy_cand_size--;
		index_in_greedy_cand[name] = 0;
		return;
	}

//printf("((((((((((((((((3333333 heap_del %d %d\n",name,heap_vc[1]);
		
	int p = index_in_greedy_cand[name];
	
	// erasing the element
	index_in_greedy_cand[name] = 0;

//	printf("(((((((((((((((( heap_del %d %d\n",name,index_in_heap_vc[name]);
	greedy_cand[p] = greedy_cand[greedy_cand_size--];

	index_in_greedy_cand[greedy_cand[p]] = p;		

//	printf("(((((((((((((((( heap_del %d %d\n",name,index_in_heap_vc[name]);

	// keep the structures of the heap
	// each item in the heap can possibly be deleted, so there are the following two cases:
	// if the previous end item is worse than one of its children
	heap_down(p);
	// if the prevous end item is better than its parent
	heap_up(p);
	// only one of the two above statements will be executed
	
//	printf("(((((((((((((((( heap_del %d %d\n",name,index_in_heap_vc[name]);
}

void heap_add(int name)
{
#ifdef debug_mode
	if(index_in_greedy_cand[name])
	{
		cout << "heap_add: input pointer error" << endl;
		exit(1);
	}
#endif
	greedy_cand[++greedy_cand_size] = name;
	index_in_greedy_cand[name] = greedy_cand_size;
	heap_up(greedy_cand_size);
#ifdef debug_mode
if(!check())
{
	cout << "heap_add: check error" << endl;
	exit(1);
}
#endif
}

int exists_elements()
{
#ifdef debug_mode
if(greedy_cand_size < 0 || greedy_cand_size > greedy_cand_capacity)
{
	cout << "illegal greedy_cand_size" << endl;
	exit(1);
}
#endif
	return greedy_cand_size;
}

int element_in(int v)
{
#ifdef debug_mode
if(index_in_greedy_cand[v] < 0 || index_in_greedy_cand[v] > greedy_cand_capacity)
{
	cout << "index of " << v << " is illegal" << endl;
	exit(1);
}
#endif
	return index_in_greedy_cand[v];
}

int size()
{
	return greedy_cand_size;
}

void show_contents()
{
	cout << "contents:" << endl;
	for(int i = 1; i <= greedy_cand_size; i++)
		cout << greedy_cand[i] << " ";
	cout << endl;
}

void init(int *score_make, int num_vars)
{
	clear();
	for(int v = 1; v <= num_vars; v++)
	{
		if(score_make[v] <= 0) continue;
		greedy_cand[++greedy_cand_size] = v;
		index_in_greedy_cand[v] = greedy_cand_size;
	}
	for(int i = greedy_cand_size; i > 0; i--)
		heap_down(i);
#ifdef debug_mode
if(!check())
{
	cout << "init: check error" << endl;
	exit(1);
}
cout << "at the end of heap_init" << endl;
#endif
}

int at(int index)
{
#ifdef debug_mode
if(index <= 0 || index > greedy_cand_size)
{
	cout << "input index illegal" << endl;
	exit(1);
}
#endif
	return greedy_cand[index];
}

int check_map()
{
	if(greedy_cand_size < 0)
	{
		cout << "greedy_cand_size error" << endl;
		return 0;
	}
	for(int i = 1; i <= greedy_cand_size; i++)
	{
		if(index_in_greedy_cand[greedy_cand[i]] != i)
		{
			cout << "location " << i << " map error." << endl;
			cout << "the element is " << greedy_cand[i] << endl;
			cout << "the index of it is " << index_in_greedy_cand[greedy_cand[i]] << endl;
			return 0;
		}
	}
	return 1;	
}

int check()
{
	if(!check_map()) return 0;
	for(int i = 1; i <= greedy_cand_size/2; i++)
	{
		if(heap_worse(greedy_cand[i], greedy_cand[i*2]) || (i*2+1 <= greedy_cand_size && heap_worse(greedy_cand[i], greedy_cand[i*2+1])))
		{
			cout << "location " << i << " heap error." << endl;
			cout << "at this location, the element is " << greedy_cand[i] << endl;
			cout << "var " << greedy_cand[i] << ", location " << i  << endl;
			cout << "var " << greedy_cand[i*2] << ", location " << i*2 << endl;		
			cout << "var " << greedy_cand[i*2+1] << ", location " << i*2+1 << endl;				
			return 0;
		}
	}
	return 1;
}

};
#endif
