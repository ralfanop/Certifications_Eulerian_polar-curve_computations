#include <stdio.h>
#include <flint/arb.h>
int main(int argc,char**argv){ FILE*f=fopen(argv[1],"r"); long m,n; char buf[4096]; int lim=argc>2?atoi(argv[2]):20;
 arb_t x; arb_init(x); int c=0;
 while(fscanf(f,"%ld %ld %[^\n]",&m,&n,buf)==3){ arb_load_str(x,buf); if(c++<lim){ printf("%ld %ld ",m,n); arb_printn(x,20,0); printf("\n");} }
 return 0;}
