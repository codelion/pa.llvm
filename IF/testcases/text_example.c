#include<limits.h>
#include<stdio.h>
#include<stdlib.h>

int* out;
#define MAX INT_MAX/2
#define OUT_SIZE 10


int gcd(a_i, c)
{
	int m, n;
	m = abs(a_i);
	n = abs(c);
	if( m == 0 ) { 
		m = MAX; 
	}
	else if(n != 0)
	{        
		while( m!= n)
		{
			if( m > n)
				m = m - n;
			else
				n = n - m;
		}
	}
	return m;
}

int get_gcd_sum(int* a, int a_len, int c) {
	int gsum, i, j;
	if( !a || a_len == 0) {
		gsum = c;
	}
	else if(a[0] == 0 && c == 0) {
		gsum = MAX;
	}
	else {
		gsum = 0;
		for( i = 0; i < a_len; i++) {      
			gsum = gsum + gcd(a[i], c);
		}
	}
	j = c % OUT_SIZE;
	out[j] = gsum/c; 
	return gsum;
}

