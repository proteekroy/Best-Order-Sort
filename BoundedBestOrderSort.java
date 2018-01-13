/**
 *	Copyright [2018] [Proteek Chandan Roy]
 * 	Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *  http://www.apache.org/licenses/LICENSE-2.0
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *    
 *  This file is a StandAlone software that implemented non-dominated sorting algorithm of the following paper
 *  Please cite this paper whenever the code is used.
 *  Bibtex entry
 *  @ARTICLE{BBOS,
	author = {Roy, Proteek Chandan and Islam, Md. Monirul and Deb, Kalyanmoy},
	journal={IEEE Transactions on Cybernetics},
	title={An Efficient Nondominated Sorting Algorithm for Large Number of Fronts},
	year={2018},
	volume={accepted},
	} 
 * @author Proteek Chandan Roy, Department of CSE, Michigan State University, USA
 * Contact: royprote@egr.msu.edu, proteek_buet@yahoo.com
 */

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;


public class BoundedBestOrderSort{

	static int m1=-1;
	static double population[][];
	static int [][]allrank;
	static MergeSort mergesort;
	static int rank[];
	static boolean []set;
	static LinkedList [][] list;
	static LinkedList []L;//two dimension
	static double value[];//two dimension
	static int totalfront = 0;
	static LinkedList[] Front;
	static int s;
	static int n;
	static int m, m2;
	static int obj,obj_rank;
	static int []size;
	static int []lex_order;
	
	
	static BoundedBinaryTree [][]nodelist;
	static BoundedBinaryTree []treeHead;
	static BoundedBinaryTree a,b,c;//for AVL rotation
	
	static double unique_solution_count[];
	static int []order_obj;
	static LinkedList[] F;

	
	static double alpha=0.2, left, right;
	static int t1=0, t2=0, t3=0, t4=0, t5 = 0, sizeA1, sizeB1, sizeC1, sizeA2, sizeB2, sizeC2, left_size, right_size;
	static boolean flipbit;
	
	static long start, end, endTime2;
	static double time, comparison, time_sort, time_rank, comparison_sort, comparison_rank;
	
	/**
	 * 
	 * @param population
	 * @param debug
	 * @param printinfo
	 * @return an object consists of information
	 * @author Proteek Roy
	 */
	public static Information best_order_sort(double [][] population, boolean debug, boolean printinfo) 
	{
		
		initialize(population, debug, printinfo);
		
		bounded_sort(debug,printinfo,n,m1);
		
		end = System.nanoTime();
		mini_stat();
		
		if(printinfo)
		{			
			System.out.println("Sorting time  = "+time_sort+" ms");
			System.out.println("Domination check time = "+time_rank+" ms");
			System.out.println("Total Running time = "+time+" ms");
			printInformation(n, m, debug, rank, comparison);
		}
		return new Information(comparison_sort, comparison_rank, time_sort, time_rank, rank);
	}
	
	
	/**
	 * Non-dominated sorting when number of objective is greater than 2
	 * @param debug
	 * @param printinfo
	 * @param n
	 * @param m
	 * @author Proteek Roy
	 */
	
	public static void bounded_sort(boolean debug, boolean printinfo,int n, int m)
	{
		int i, j, total=0;
		boolean dominated;
		Node head;
		BoundedBinaryTree headnode, tailnode;

		rank = new int[n];
		set=new boolean[n];
		
		nodelist = new BoundedBinaryTree[m][n];
		allrank = new int[n][m];
		lex_order = new int[n];

		treeHead = new BoundedBinaryTree[m];
		unique_solution_count = new double[m];
		order_obj = new int[m];
		
		for(j=0;j<m;j++)
		{
			treeHead[j] = new BoundedBinaryTree();
			treeHead[j].data = new LinkedList();
			nodelist[j][0] = treeHead[j];
			nodelist[j][0].rank = 0;
			
			for(i=1;i<n;i++)
			{
				allrank[i][j]=i;
				nodelist[j][i] = new BoundedBinaryTree();
				nodelist[j][i-1].rightnode = nodelist[j][i];
				nodelist[j][i].parent = nodelist[j][i-1];
				
				nodelist[j][i].data = new LinkedList();
				nodelist[j][i].rank = i;
			}
			order_obj[j] = j;
		}

		size = new int[m];
		
		mergesort.setrank(allrank);
		start=System.nanoTime();
		sortingValues();
		endTime2 = System.nanoTime();
		
		
		//Finding the order of comparison
		for(i=0;i<n;i++)
		{
			for(j=0;j<m;j++)
			{
				s = allrank[i][j];
				if(!set[s])
				{
					total++;
					set[s] = true;
					unique_solution_count[j]--;
				}
			}
			if(total==n)
			{
				break;
			}
		}
		for(i=0;i<n;i++)//for all solutions
		{
			set[i] = false;
		}
		
		mergesort.setMinRank(unique_solution_count);
		mergesort.setBestrank(order_obj);
		mergesort.mergesortbest(0,m-1);
		order_obj = mergesort.bestrank;//now we know which one is best
		
		
		for(i=0;i<total;i++)//n
		{
			for(obj=0;obj<m;obj++)
			{
				s = allrank[i][obj];
				
				if(set[s])//s2 is already ranked
				{
					nodelist[obj][rank[s]].data.addStart(s);
					nodelist[obj][rank[s]].size++;

					if(rank[s]>size[obj])
						size[obj]=rank[s];
					
					headnode = nodelist[obj][rank[s]].parent;
					while(headnode!=null)
					{
						headnode.size++;
						headnode = headnode.parent;
					}
					
					continue;
				}
				set[s]=true;
				
				
				headnode = treeHead[obj];	
				
				while(true)
				{
					
					dominated = false;
					head = headnode.data.start;
					
					while(head!=null)
					{
						if(dominates(head.data,s))
						{
							dominated = true;
							break;
						}
						head = head.link;
					}
					if(!dominated) //not dominated
					{
						if(headnode.leftnode==null)//if it is leftmost node of a subtree
						{
							rank[s] = headnode.rank;
							headnode.data.addStart(s);//size increased already
							
							tailnode = headnode;
							while(tailnode!=null)
							{
								tailnode.size++;
								tailnode = tailnode.parent;
							}
							if(size[obj]>2 && headnode.parent!=null && headnode.parent.parent!=null)
							{
								rebalance(headnode.parent.parent);
							}
							
							break;
						}
						else
						{
							headnode = headnode.leftnode;
						}
					}
					else //dominated
					{
						if(headnode.rank<size[obj])
						{
							if(headnode.rightnode==null)//if it is rightmost node of a subtree
							{
								rank[s] = headnode.rank+1;
								nodelist[obj][rank[s]].data.addStart(s);
	
								tailnode = nodelist[obj][rank[s]];
								while(tailnode!=null)
								{
									tailnode.size++;
									tailnode = tailnode.parent;
								}
								if(size[obj]>2 && headnode.parent!=null)
								{
									rebalance(headnode.parent);
								}
								break;
							}
							else
							{
								headnode = headnode.rightnode;
							}
							
						}
						else //if it is rightmost node(with highest rank)
						{
							size[obj]++;
							rank[s] = size[obj];
							nodelist[obj][rank[s]].data.addStart(s);
							nodelist[obj][rank[s]].size++;
							
							tailnode = headnode;
							while(tailnode!=null)
							{
								tailnode.size++;
								tailnode = tailnode.parent;
							}
							
							if(size[obj]>2 && headnode.parent!=null)
							{
								rebalance(headnode.parent);
							}
							
							break;	
						}
							
					}
				}//while(true)
			}
		}
	}
	
	/**
	 * Rebalance operation when solutions on the left is different from
	 * solutions on the right by a factor alpha
	 * @param headnode
	 * @author Proteek Roy
	 */
	public static void rebalance(BoundedBinaryTree headnode)
	{
		flipbit = false;
		if(headnode.rightnode==null)
		{
			right_size=0;
		}
		else
		{
			right_size = headnode.rightnode.size;
		}
		if(headnode.leftnode==null)
		{
			left_size = 0;
		}
		else
		{
			left_size = headnode.leftnode.size;
		}
		
		
		if(left_size<alpha*right_size)//right node has more leaves
		{
			if(headnode.rightnode.leftnode!=null)//right-left case
			{		
				if(headnode.rightnode.leftnode.leftnode==null)
				{
					t3 = 0;
				}
				else
					t3 = headnode.rightnode.leftnode.leftnode.size;
				
				if(headnode.rightnode.leftnode.rightnode==null)
				{
					t4 = 0;
				}
				else
					t4 = headnode.rightnode.leftnode.rightnode.size;

				sizeA2 = t3 + headnode.size - headnode.rightnode.size;
				sizeB2 = t4 + headnode.rightnode.size - headnode.rightnode.leftnode.size;
				

				headnode.size =  sizeA2;//a
				headnode.rightnode.size  = sizeB2;//b
				headnode.rightnode.leftnode.size = sizeA2 + sizeB2 + headnode.rightnode.leftnode.size - (t3+t4);	
				headnode = doubleRightLeftRotation(headnode);
				flipbit = true;
		
			}
			else //right-right case
			{	
				
				if(headnode.rightnode.leftnode==null)
					t2 = 0;
				else
					t2 = headnode.rightnode.leftnode.size;
				
				sizeA2 = headnode.size +  t2 - headnode.rightnode.size;

				headnode.size = sizeA2 ;//a
				headnode.rightnode.size = headnode.rightnode.size + sizeA2 - t2;//b	
				headnode = rotateLeft(headnode);
				flipbit = true;
			}
		}
		else if(right_size<alpha*left_size)//left node has more leaves
		{
			if(headnode.leftnode.rightnode!=null)// left-right case
			{
				t1 = 0;
				if(headnode.leftnode.rightnode.leftnode==null)
				{
					t3 = 0;
				}
				else
				{
					t3 = headnode.leftnode.rightnode.leftnode.size;
				}
				if(headnode.leftnode.rightnode.rightnode==null)
				{
					t4 = 0;
				}
				else
				{
					t4 = headnode.leftnode.rightnode.rightnode.size;
				}
				//size after
				sizeA2 = t4 + headnode.size - headnode.leftnode.size;
				sizeB2 = t3 + headnode.leftnode.size - headnode.leftnode.rightnode.size;
				headnode.leftnode.rightnode.size = headnode.leftnode.rightnode.size - (t3+t4) + sizeA2 + sizeB2;//size'(c)
				headnode.size =  sizeA2;//size'(a)
				headnode.leftnode.size  = sizeB2;//size'(b)
				headnode = doubleLeftRightRotation(headnode);
				flipbit = true;
			}
			else //left-left case
			{
				if(headnode.leftnode.rightnode==null)
				{
					t2 = 0;
				}
				else
				{
					t2 = headnode.leftnode.rightnode.size;
				}
				sizeA2 = headnode.size + t2 - headnode.leftnode.size;
				headnode.size = sizeA2;//a
				headnode.leftnode.size = headnode.leftnode.size + sizeA2 - t2;//b
				headnode = rotateRight(headnode);
				flipbit = true;
			}
		}
		
		if (headnode.parent != null) 
		{
			if(flipbit == true)
			{
				rebalance(headnode.parent);
			}
	    }
		else //if (headnode.parent == null) 
	    {
			treeHead[obj] = headnode;
	    }
		
		return;
	}
	
	/**
	 * 
	 * @param a
	 * @return
	 * @author Proteek Roy
	 */
	private static BoundedBinaryTree rotateLeft(BoundedBinaryTree a)//right-right case 
	{
		 
		BoundedBinaryTree b = a.rightnode;
        b.parent = a.parent;
 
        a.rightnode = b.leftnode;
 
        if (a.rightnode != null)
        {
            a.rightnode.parent = a;
        }
        
        b.leftnode = a;
        a.parent = b;
 
        if (b.parent != null) {
            if (b.parent.rightnode == a) {
                b.parent.rightnode = b;
            } else {
                b.parent.leftnode = b;
            }
        }
 
        return b;
    }
 
	/**
	 * 
	 * @param a
	 * @return
	 * @author Proteek Roy
	 */
    private static BoundedBinaryTree rotateRight(BoundedBinaryTree a) //left-left case
    {
 
    	BoundedBinaryTree b = a.leftnode;
        b.parent = a.parent;
 
        a.leftnode = b.rightnode;
 
        if (a.leftnode != null)
        {
            a.leftnode.parent = a;
        }
        
        b.rightnode = a;
        a.parent = b;
 
        if (b.parent != null) {
            if (b.parent.rightnode == a) {
                b.parent.rightnode = b;
            } else {
                b.parent.leftnode = b;
            }
        }
        return b;
    }
    /**
     * 
     * @param a
     * @return
     * @author Proteek Roy
     */
    private static BoundedBinaryTree doubleRightLeftRotation(BoundedBinaryTree a) //rotateRightLeft
    {
 
    	BoundedBinaryTree c = a.rightnode.leftnode;
    	BoundedBinaryTree b = a.rightnode; 
       
 
        a.rightnode = c.leftnode;
        c.leftnode = a;
        if (a.rightnode != null)
        {
            a.rightnode.parent = a;
        }
        
        b.leftnode = c.rightnode;
        c.rightnode = b;
        if (b.leftnode != null)
        {
        	b.leftnode.parent = b;
        }
        
        c.parent = a.parent;
        b.parent = c;
        a.parent = c;
       
        if (c.parent != null) {
            if (c.parent.rightnode == a) {
                c.parent.rightnode = c;
            } else {
                c.parent.leftnode = c;
            }
        }
        return c;
    }
    
    /**
     * 
     * @param a
     * @return
     * @author Proteek Roy
     */
    private static BoundedBinaryTree doubleLeftRightRotation(BoundedBinaryTree a) //rotateRightLeft
    {
 
    	BoundedBinaryTree c = a.leftnode.rightnode;
    	BoundedBinaryTree b = a.leftnode;
 

 
        a.leftnode = c.rightnode;
        c.rightnode = a;
 
        if (a.leftnode != null)
        {
            a.leftnode.parent = a;
        }
        
        b.rightnode = c.leftnode;
        c.leftnode = b;
        if ( b.rightnode != null)
        {
        	 b.rightnode.parent = b;
        }
        
        c.parent = a.parent;
        b.parent = c;
        a.parent = c;
        
        
        if(c.parent != null) {
            if (c.parent.rightnode == a) {
                c.parent.rightnode = c;
            } else {
                c.parent.leftnode = c;
            }
        }
        return c;
    }

	
	/**
	 * Non-domination check, Although previously sorted by lexicographic order
	 * it may be true that those solutions are identical
	 * @param p1
	 * @param p2
	 * @return
	 * @author Proteek Roy
	 */
	public static boolean dominates(int p1, int  p2)//one way domination check
	{
		boolean equal = true;
		int i;
		for(i=0;i<m;i++)
		{
			
			if(population[p1][i] > population[p2][i])
			{
				comparison_rank++;
				return false;
			}
			else if(equal && population[p1][i] < population[p2][i])
			{
				comparison_rank = comparison_rank+2;
				equal = false;
			}
		}
		
		if(equal)//both solutions are equal
			return false;
		else //dominates
			return true;
	}
	/**
	 * Sorting population by each objective
	 * @author Proteek Roy
	 */
	public static void sortingValues() 
	{
		int j;
		mergesort.sort(0);//Sorting first objectives and get lexicographic order
		allrank=mergesort.getrank();
		for(j=1;j<n;j++)
		{
			lex_order[allrank[j][0]] = j;  
		}
		mergesort.setLexOrder(lex_order);
		for (j=1;j<m1;j++)
		{
			mergesort.sort_specific(j);
			comparison = comparison + mergesort.comparison;
		}
		allrank = mergesort.getrank();
	}
	
	/**
	 * Initialize all variables
	 * @param population
	 * @param debug
	 * @param printinfo
	 * @author Proteek Roy
	 */
	private static void initialize(double[][] population2, boolean debug, boolean printinfo)
	{
		if(printinfo)
		{
			System.out.println("\nStarting Bounded Best Order Sort");
		}
		population = population2;
		mergesort = new MergeSort();
		n = population.length;
		m = population[0].length;
		mergesort.setPopulation(population);
		comparison=0;
		m1 = m;//change this value to m1 = log(n) when m is very high
	}
	/**
	 * Calculation of time and other possible statistics
	 * @author Proteek Roy
	 */
	private static void mini_stat()
	{
		time = (end-start)*1.0/1000000.0;
		time_sort = (endTime2 - start)*1.0/1000000.0;
		time_rank = (end - endTime2)*1.0/1000000.0;
		comparison = comparison_sort + comparison_rank;
	}
		
	/**
	 * This algorithm runs O(nlogn) algorithm for two dimensional non-dominated sorting problem
	 * @author Proteek Roy
	 */
	public static void extended_kung_sort_two_dimension()
	{
		//Initialization
		int i,j, low, high, middle;
		double key;
		
		rank = new int[n];//ranks of solutions
		allrank = new int[n][m];//partial lexicographical ordering of x-axis values 
		value = new double[n];
		L = new LinkedList[n];
		for(j=0;j<m;j++)
		{
			for(i=0;i<n;i++)
			{
				allrank[i][j]=i;
			}
		}
		start = System.nanoTime();
		mergesort.setrank(allrank);
		start=System.nanoTime();	
		mergesort.sort(0);;//lexicographic sort
		endTime2 = System.nanoTime();
		comparison_sort = comparison_sort + mergesort.comparison;
		
		
		value[0] = population[allrank[0][0]][1];//y-value of first rank solution
		rank[allrank[0][0]] = 0; //rank of first solution is already found
		totalfront = 1;
		L[0] = new LinkedList();
		for(i=1;i<n;i++)
		{
			s = allrank[i][0];//take the solution id
			key = population[s][1];//the field we would consider
			
			//-------------Go over all points----------------------//
			low = 0;			
			high = totalfront - 1;
		         
			while(high >= low) 
			{
				middle = low + ((high - low) / 2); 
					
				if(key < value[middle]) //it has low rank, numerically
				{
					comparison_rank++;
					high = middle - 1;
				}
				if(key >= value[middle]) //it has high rank, numerically
				{
					comparison_rank = comparison_rank+2;
					low = middle + 1;
				}
			}
				
			if(low==totalfront)
			{
				totalfront = totalfront+1;
			}
			rank[s] = low;
			value[low] = key;
		}
	}
	
	/**
	 * Class that takes care of lexicographic sorting of objectives 
	 * @author Proteek Roy
	 *
	 */
	static class MergeSort 
	{
		//local variables
		int[] helper;
		double [][]population;
		int n;
		int left;
		int right;
		int largest;
		int obj;
		boolean check;
		int [][] rank;
		int comparison;
		int [] lex_order;
		double []min_rank;
		int [] bestrank;
		
		
		public void setrank(int [][] rank)//set ranking information
		{
			this.rank=rank;
		}
		public int[][] getrank()//get ranking information
		{
			return rank;
		}
		
		public void setPopulation(double [][]pop)//set local population
		{
			this.population=pop;
			this.n=population.length;
			helper=new int[n];
		}
		
		public void setLexOrder(int []order)
		{
			this.lex_order = order;
		}
		public void setBestrank(int []b)
		{
			this.bestrank=b;
			helper = new int[b.length];
		}
		public void setMinRank(double []min_rank)
		{
			this.min_rank = min_rank;
		}
		
		/**
		 * Sort objectives obj
		 * @param obj
		 * @author Proteek Roy
		 */
		
		public void sort(int obj)//merge sort main
		{
			this.obj=obj;
			comparison = 0;
			n = population.length;
			mergesort(0, n-1);
		}
		
		/**
		 * merge sort algorithm O(nlogn) sorting time
		 * @author Proteek Roy
		 */
		private void mergesort(int low, int high) 
		{
			// check if low is smaller then high, if not then the array is sorted
			if (low < high) 
			{
				// Get the index of the element which is in the middle
				int middle = low + (high - low) / 2;
				// Sort the left side of the array
				mergesort(low, middle);
				// Sort the right side of the array
				mergesort(middle + 1, high);
				// Combine them both
				merge(low, middle, high);
			 }
		}
		
		/**
		 * 
		 * @param low
		 * @param middle
		 * @param high
		 * @author Proteek Roy
		 */
		private void merge(int low, int middle, int high) 
		{
			// Copy both parts into the helper array
			for (int i = low; i <= high; i++) 
			{
				helper[i] = rank[i][obj];
			}
			  
			int i = low;
			int j = middle + 1;
			int k = low;
			// Copy the smallest values from either the left or the right side back
			// to the original array
			while (i <= middle && j <= high) 
			{
				if (population[helper[i]][obj] < population[helper[j]][obj]) 
				{
					comparison++;
					rank[k][obj] = helper[i];
					i++;
				} 
				else if(population[helper[i]][obj] > population[helper[j]][obj]) 
				{
					comparison = comparison+2;
					rank[k][obj] = helper[j];
					j++;
				}
				else //two values are equal
				{
					comparison = comparison+2;
					check=lexicopgraphic_dominate(helper[i],helper[j]);
					if(check)
					{
						rank[k][obj] = helper[i];
						i++;
					}
					else
					{
						rank[k][obj] = helper[j];
						j++;
					}
				}
				k++;
			}
			while(i<=middle)
			  {
				  rank[k][obj]=helper[i];
				  k++;
				  i++;
			  }
			  while(j<=high)
			  {
				  rank[k][obj]=helper[j];
				  k++;
				  j++;
			  }

		}
		
		/**
		 * 
		 * @param obj
		 * @author Proteek Roy
		 */
		public void sort_specific(int obj)//uses lexicographical order of 1st dimension
		{
			this.obj=obj;
			n = population.length;
			comparison = 0;
			mergesort_specific(0, n-1);
		}
		
		/**
		 * Merge sort with the help of lexicographic order got by sorting first objectives
		 * @param low
		 * @param high
		 * @author Proteek Roy
		 */
		private void mergesort_specific(int low, int high) 
		{
			  // check if low is smaller then high, if not then the array is sorted
			  if (low < high) 
			  {
				  // Get the index of the element which is in the middle
				  int middle = low + (high - low) / 2;
				  // Sort the left side of the array
				  mergesort_specific(low, middle);
				  // Sort the right side of the array
				  mergesort_specific(middle + 1, high);
				  // Combine them both
				  merge_specific(low, middle, high);
			  }
			  
		}
		/**
		 * 
		 * @param low
		 * @param middle
		 * @param high
		 * @author Proteek Roy
		 */
		private void merge_specific(int low, int middle, int high) 
		{
			for (int i = low; i <= high; i++) 
			{
				helper[i] = rank[i][obj];
			}
			  
			int i = low;
			int j = middle + 1;
			int k = low;
			
			while (i <= middle && j <= high) 
			{
				if (population[helper[i]][obj] < population[helper[j]][obj]) 
				{
					comparison++;
					rank[k][obj] = helper[i];
					i++;
				} 
				else if(population[helper[i]][obj] > population[helper[j]][obj]) 
				{
					comparison = comparison+2;
					rank[k][obj] = helper[j];
					j++;
				}
				else //two values are equal
				{			  
					comparison = comparison+2;
					if(lex_order[helper[i]]<lex_order[helper[j]])
					{
						rank[k][obj] = helper[i];
						i++;
					}
					else
					{
						rank[k][obj] = helper[j];
						j++;
					}
				}
				k++;
			}
			while(i<=middle)
			{
				rank[k][obj] = helper[i];
				k++;
				i++;
			}
			while(j<=high)
			{
				rank[k][obj] = helper[j];
				k++;
				j++;
			}

		}
		
		/**
		 * 
		 * @param low
		 * @param high
		 * @author Proteek Roy
		 */
		public void mergesortbest(int low, int high) 
	  	{
	  		// check if low is smaller then high, if not then the array is sorted
	  		if (low < high) 
	  		{
	  			// Get the index of the element which is in the middle
	  			int middle = low + (high - low) / 2;
	  			// Sort the left side of the array
	  			mergesortbest(low, middle);
	  			// Sort the right side of the array
	  			mergesortbest(middle + 1, high);
	  			// Combine them both
	  			mergebest(low, middle, high);
	  		}	  
	  	}
		
		/**
		 * 
		 * @param low
		 * @param middle
		 * @param high
		 * @author Proteek Roy
		 */
	  	private void mergebest(int low, int middle, int high) 
	    {
	  	  for (int i = low; i <= high; i++) 
	  	  {
	  		  helper[i] = bestrank[i];
	  	  }
	  	  
	  	  int i = low;
	  	  int j = middle + 1;
	  	  int k = low;
	  	  
	  	  while (i <= middle && j <= high) 
	  	  {
	  		  
	  		  if (min_rank[helper[i]] < min_rank[helper[j]]) 
	  		  {
	  			  bestrank[k] = helper[i];
	  			  i++;
	  		  } 
	  		  else
	  		  {
	  			  bestrank[k] = helper[j];
	  			  j++;
	  		  }
	  		  k++;
	  	  }
	  	  while(i<=middle)
	  	  {
	  		  bestrank[k] = helper[i];
	  		  k++;
	  		  i++;
	  	  }
	  	  while(j<=high)
	  	  {
	  		  bestrank[k] = helper[j];
	  		  k++;
	  		  j++;
	  	  }

	    }

		/**
		 * check whether p1 lexicographically dominates p2
		 * @param p1
		 * @param p2
		 * @return
		 * @author Proteek Roy
		 */
		public boolean lexicopgraphic_dominate(int p1, int p2)
		{
			int i;

			for(i=0;i<population[0].length;i++)
			{
				comparison++;
				if(population[p1][i] == population[p2][i])
					continue;
				else if(population[p1][i] < population[p2][i])
				{
					return true;
				}
				else
				{
					return false;
				}
			}
			
			return true;
	 	}
	  	
	}

	/**
	 * Read population from a text file separated by whitespace e.g tab/space, one solution per line
	 * @param n, size of population
	 * @param m, objective of population
	 * @param filename, name of text file
	 * @param population, memory to hold population
	 * @author Proteek Roy
	 */
	public static void read_population(int n, int m, String filename,double [][] population) 
	{
		int i=0,j;
		try
		{
			BufferedReader br = new BufferedReader(new FileReader(filename));
			String strLine;
			while ((strLine = br.readLine()) != null)   
			{
				
				String[] tokens = strLine.split("\\s+");
				strLine=strLine.trim();
				if(i==n)
				{
					break;
				}
				for(j=0;j<m;j++)
				{
					try{
					population[i][j]=Double.parseDouble(tokens[j]);
					}
					catch (Exception e)
					{
						System.err.println("Error: " + e.getMessage());
					}
				}
				i++;
			}
			br.close();
		}
		catch (IOException e)
		{
			System.err.println("Error: " + e.getMessage());
		}
	}
	/**
	 * Class to save solutions in a list
	 * @author Proteek Roy
	 *
	 */
	public static class LinkedList
	{
	    protected Node start;
	    
	    public LinkedList()// Constructor
	    {
	        start = null;
	    }
	    
	    //Function to insert an element at the beginning 
	    public void addStart(int val)
	    {
	        Node nptr = new Node(val, start);    
	        start = nptr;
	    }
	}
	
	/**
	 * Object that stores one solution
	 * @author Proteek
	 *
	 */
	public static class Node
    {
        protected int data;
        protected Node link;
        
        //  Constructor
        public Node(int d,Node n)
        {
            data = d;
            link = n;
        }
    }
	
	/**
	 * Tree to store Rank numbers
	 * @author Proteek
	 *
	 */
	private static class BoundedBinaryTree
	{
		protected BoundedBinaryTree leftnode, rightnode, parent;
		
		protected int size, rank;
		LinkedList data;
		public BoundedBinaryTree()
		{
			parent = null;
			leftnode = null;
			rightnode = null;
			size = 0;
			rank = 0;
			data = null;
			
		}
	}
	
	/**
	 * This class is intended to provide information
	 * @author Proteek Roy
	 *
	 */
	public static class Information 
	{
		public static double comparison = 0;
		public static double time = 0;
	    public static double comparison_sort = 0;
	    public static double comparison_rank = 0;
	    public static double time_sort = 0;
	    public static double time_rank = 0;
	    public static int[] R;
	    
	    public Information(double comparison_sort1, double comparison_rank1, double time_sort1, double time_rank1, int[] R1)
	    {
	    	comparison_sort = comparison_sort1;
	 	    comparison_rank = comparison_rank1;
	 	    time_sort = time_sort1;
	 	    time_rank = time_rank1;
	 	    comparison = comparison_sort + comparison_rank;
	 	    time = time_sort + time_rank;
	 	    R = R1;
	    }
	}
	/**
	 * Printing all solutions from each front
	 * @param n
	 * @param m
	 * @param debug
	 * @param rank
	 * @param totalfront
	 * @param comparison_dominated
	 * @author Proteek Roy
	 */
	public static void printInformation(int n, int m, boolean debug, int []rank, double comparison)
	{
		int i,k, k1;
		Node head;
		
		totalfront = 0;
		for(i=0;i<n;i++)
		{
			if(rank[i]>totalfront)
			{
				totalfront = rank[i];
			}
			
		}
		totalfront++;
		
		LinkedList[] F=new LinkedList[totalfront];
		
		for(i=0;i<totalfront;i++)
		{
			F[i]=new LinkedList();
		}
		for(i=0;i<n;i++)
		{
			F[rank[i]].addStart(i);
		}
		
		
		for(i=0;i<totalfront;i++)
		{
			if(F[i]==null)
				break;
			if(F[i].start==null)
				break;
			head = F[i].start;
			k=0;
			while(head!=null)
			{
				k++;
				head=head.link;
			}
			System.out.println("Number of elements in front ["+(i+1)+"] is "+k);
			if(debug)
			{
				k1 = 0;
				if(F[i].start!=null)
				{
					System.out.print(" --> ");
					head = F[i].start;	
					while(head!=null)
					{
						k1++;
						System.out.print((head.data)+", ");
						head=head.link;
						if(k1%30==0)
							System.out.println();
					}
					System.out.println();
				}
			}
		}
		System.out.println("Number of fronts = "+totalfront);
		System.out.println("Number of Comparisons for  domination = "+comparison);
		System.out.println("Total Number of elements is "+n);
		System.out.println("Total Number of objectives is "+ m);
	}
	
	/**
	 * Main Function
	 * @param args
	 * @author Proteek Roy
	 */
	public static void main(String[] args) 
	{
		/*
		int i, j;
		int n = 1000;
		int m = 2;
		int f = 50;
		boolean printinfo = true;//print overall information
		boolean debug = false;//print out elements of a front	
		String filename="fixed_front_"+n+"_"+m+"_"+f+"_1.txt";
		//String filename="cloud_"+n+"_"+m+"_1.txt";
		double [][] population = new double[n][m];
		BoundedBestOrderSort.read_population(n,m,filename, population);
		*/
		
		int i,j,k;
		int n = 15;
		int m = 5;
		int f = 1;
		boolean printinfo = true;//print overall information
		boolean debug = false;//print out elements of a front
		double [][]population = new double[n][m];
		/*
		population[0][1] = 2;	population[0][2] = 4;	population[0][3] = 3;	population[0][4] = 2;	population[0][0] = 3;	
		population[1][1] = 4;	population[1][2] = 3;	population[1][3] = 2;	population[1][4] = 5;	population[1][0] = 1;
		population[2][1] = 1;	population[2][2] = 1;	population[2][3] = 1;	population[2][4] = 1;	population[2][0] = 1;
		population[3][1] = 1;	population[3][2] = 5;	population[3][3] = 5;	population[3][4] = 3;	population[3][0] = 2;
		population[4][1] = 1;	population[4][2] = 2;	population[4][3] = 3;	population[4][4] = 1;	population[4][0] = 5;
		population[5][1] = 3;	population[5][2] = 2;	population[5][3] = 1;	population[5][4] = 1;	population[5][0] = 5;
		population[6][1] = 3;	population[6][2] = 1;	population[6][3] = 1;	population[6][4] = 1;	population[6][0] = 5;
		population[7][1] = 2;	population[7][2] = 5;	population[7][3] = 3;	population[7][4] = 2;	population[7][0] = 3;
		*/
		
		for(i=0;i<n;i++)
		{
			for(j=0;j<m;j++)
			{
				if(i<5)
				{
					population[i][j] = 3;
				}
				else if(i<10)
				{
					population[i][j] = 1;
				}
				else
				{
					population[i][j] = 2;
				}
			}
		}
		
		
		BoundedBestOrderSort.best_order_sort(population, debug, printinfo);;
		
	}
	

}
