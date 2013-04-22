#include<limits.h>
#include<stdio.h>
#include<stdlib.h>

int* out;
#define MAX INT_MAX/2
#define OUT_SIZE 10


int gcd(a_i, c) //h, l
{
	int m, n; //l
	m = abs(a_i); //h
	n = abs(c); //h
	if( m == 0 ) { //h
		m = MAX; //h
	}//l
	else if(n != 0)//h
	{        
		while( m!= n) //h, l
		{
			if( m > n)//h
				m = m - n;//h, l
			else
				n = n - m;//h, l
		}//l
	}//l
	return m;//h
}

int get_gcd_sum(int* a, int a_len, int c) { //h,l
	int gsum, i, j; //l
	if( !a || a_len == 0) { //h
		gsum = c; //h
	} //l
	else if(a[0] == 0 && c == 0) { //h
		gsum = MAX; //h
	} //l
	else { 
		gsum = 0; //h
		for( i = 0; i < a_len; i++) { //h, l
			gsum = gsum + gcd(a[i], c); //h
		}
	}
	j = c % OUT_SIZE; //h
	out[j] = gsum/c; //h, l
	return gsum; //h
}

