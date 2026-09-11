/* Exact little-endian nonnegative integer multiplication for Kronecker packing.
   Build: gcc -O2 -fPIC -shared kronecker_gmp.c -lgmp -o kronecker_gmp.so
   This speeds coefficient arithmetic only; it is not a decomposition solver. */
#include <gmp.h>
#include <stddef.h>
#include <string.h>
int m16_multiply(const unsigned char *a,size_t na,const unsigned char *b,size_t nb,
                 unsigned char *out,size_t capacity){
    if(!out || !a || !b || !capacity)return -1;
    mpz_t x,y,z;mpz_inits(x,y,z,NULL);
    mpz_import(x,na,-1,1,0,0,a);mpz_import(y,nb,-1,1,0,0,b);mpz_mul(z,x,y);
    size_t need=(mpz_sizeinbase(z,2)+7)/8;
    if(need>capacity){mpz_clears(x,y,z,NULL);return -2;}
    memset(out,0,capacity);size_t written=0;mpz_export(out,&written,-1,1,0,0,z);
    mpz_clears(x,y,z,NULL);return 0;
}
