#include <iostream>
#include <wmmintrin.h>
#include <immintrin.h>
#include <emmintrin.h>
#include <pmmintrin.h>
#include <string.h>
#define ALIGN(n) __attribute__ ((aligned(n)))
#define pipeline 1
#define swap_if_le(b) \
      _mm_shuffle_epi8(b,_mm_set_epi8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15))

#define EXPAND_ASSIST(v1,v2,v3,v4,shuff_const,aes_const)                    \
    v2 = _mm_aeskeygenassist_si128(v4,aes_const);                           \
    v3 = _mm_castps_si128(_mm_shuffle_ps(_mm_castsi128_ps(v3),              \
                                         _mm_castsi128_ps(v1), 16));        \
    v1 = _mm_xor_si128(v1,v3);                                              \
    v3 = _mm_castps_si128(_mm_shuffle_ps(_mm_castsi128_ps(v3),              \
                                         _mm_castsi128_ps(v1), 140));       \
    v1 = _mm_xor_si128(v1,v3);                                              \
    v2 = _mm_shuffle_epi32(v2,shuff_const);                                 \
    v1 = _mm_xor_si128(v1,v2)

#define PRE_COMP_BLOCKS 31     /* Must be between 0 and 31 */
static inline unsigned ntz(unsigned x) {
		static const unsigned char tz_table[32] =
		{ 0,  1, 28,  2, 29, 14, 24, 3, 30, 22, 20, 15, 25, 17,  4, 8,
		 31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18,  6, 11,  5, 10, 9};
		return tz_table[((uint32_t)((x & -x) * 0x077CB531u)) >> 27];
	}

typedef ALIGN(16) __m128i block;

using namespace std;
static void AES_128_Key_Expansion(const unsigned char *userkey, void *key);
static inline void AES_encrypt(__m128i tmp, __m128i *out,__m128i *key, unsigned rounds);
static void imprimiArreglo(int tam, unsigned char *in );
static void shift_left(unsigned char *x);
static void shift_right(unsigned char *x);
// static inline __m128i double_block(__m128i bl);
// static inline __m128i swap_if_le(__m128i b);
void pmac_aes_init(unsigned char *K_1,unsigned tag_len);        
static void PMAC(unsigned char *K_1, unsigned char *M, int size, unsigned char *T);
block L[PRE_COMP_BLOCKS+1];     /* Precomputed L(i) values, L[0] = L */
block L_inv;                    /* Precomputed L/x value             */


#define test 34

int main(){
    
    ALIGN(64) unsigned char plaintext[test];
    for (int i = 0; i < test; i++)
    {
        plaintext[i]=i;
    }
    
    ALIGN(16) unsigned char tag[16 ]={ 0x00,0x01,0x02,0x03,
                                       0x04,0x05,0x06,0x07,
                                       0x08,0x09,0x0a,0x0b,
                                       0x0c,0x0d,0x0e,0x0f};
    ALIGN(16) unsigned char K_1[16 ]={ 0x00,0x01,0x02,0x03,
                                       0x04,0x05,0x06,0x07,
                                       0x08,0x09,0x0a,0x0b,
                                       0x0c,0x0d,0x0e,0x0f};
    ALIGN(16) unsigned char N[16 ]={ 0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0};


    imprimiArreglo(test, plaintext);

    pmac_aes_init(K_1,16);        

    // PMAC(K_1, N, plaintext, 64, tag);
    PMAC(K_1, plaintext, test, tag);

    printf("\n");
    imprimiArreglo(16, tag);
    return 0;
}


static void PMAC(unsigned char *K_1, unsigned char *M, int size, unsigned char *T){

    int m_blocks = 0;
    if (size%16==0)
        m_blocks=(size/16);
    else
        m_blocks=(size/16) + 1;
    int size_copy=size;
    static __m128i * plain_text = (__m128i*) M;
    unsigned char tmp_2[16] = {0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0};
    __m128i tmp;
    __m128i Offset;
    __m128i Tag;
    __m128i checksum;
    __m128i keys_128[11];
    __m128i sum_nonce= _mm_set_epi32(0,0,0,1);

    AES_128_Key_Expansion(K_1, keys_128);
    checksum = _mm_setzero_si128();
    Tag = _mm_setzero_si128();
    Offset = _mm_setzero_si128();
    int i=0;
    for (i = 1; i < m_blocks; i++){

        Offset = _mm_xor_si128( L[ntz(i)] ,Offset);        
        
        plain_text[i-1]=_mm_xor_si128(plain_text[i-1],Offset);
        
        AES_encrypt(plain_text[i-1], &plain_text[i-1], keys_128, 10);

        checksum =_mm_xor_si128(plain_text[i-1],checksum);
        size_copy-=16;

    }


    if (size_copy==16){
        checksum = _mm_xor_si128( plain_text[i] ,checksum);        
        checksum = _mm_xor_si128( L_inv ,checksum);        
    
    }else{
        // imprimiArreglo(test,M);

        memcpy(tmp_2, M+((i-1)*16) , size_copy);
        int k=0;
        
        // for (int j = (i-1)*16; j < (i-1)*16+size_copy; j++)
        // {
        //     printf("%x", M[j]);
        // }
        
        tmp_2[size_copy]=0x80;
        // imprimiArreglo(16,tmp_2);

        tmp = _mm_setzero_si128();
        tmp = _mm_load_si128((__m128i *)&tmp_2);
        // imprimiArreglo(16,(unsigned char *)&checksum);
        // imprimiArreglo(16,(unsigned char *)&tmp);
        checksum = _mm_xor_si128( tmp ,checksum); 
    }
    
    

    AES_encrypt(checksum, &Tag, keys_128, 10);
	_mm_store_si128 ((__m128i*)T,Tag);
}


static inline void AES_encrypt(__m128i tmp, __m128i *out,__m128i *key, unsigned rounds){
	int j;
	tmp = _mm_xor_si128 (tmp,key[0]);
	for (j=1; j<rounds; j++)  tmp = _mm_aesenc_si128 (tmp,key[j]);
	tmp = _mm_aesenclast_si128 (tmp,key[j]);
	_mm_store_si128 ((__m128i*)out,tmp);
}


static void AES_128_Key_Expansion(const unsigned char *userkey, void *key)
{
    __m128i x0,x1,x2;
    __m128i *kp = (__m128i *)key;
    kp[0] = x0 = _mm_loadu_si128((__m128i*)userkey);
    x2 = _mm_setzero_si128();
    EXPAND_ASSIST(x0,x1,x2,x0,255,1);   kp[1]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,2);   kp[2]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,4);   kp[3]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,8);   kp[4]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,16);  kp[5]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,32);  kp[6]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,64);  kp[7]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,128); kp[8]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,27);  kp[9]  = x0;
    EXPAND_ASSIST(x0,x1,x2,x0,255,54);  kp[10] = x0;
}



void imprimiArreglo(int tam, unsigned char *in )
{

    for (int i = 0; i<tam; i++){
        printf("%02x", in[i] );
    }
    printf("\n" );

}


/************************************************************************* 
 * ocb_aes_init 
 *************************************************************************/
// keystruct *                         /* Init'd keystruct or NULL      */
void pmac_aes_init(unsigned char   *K_1,    /* AES key                       */
             unsigned   tag_len    /* Length of tags to be used     */
             )        /* OCB key structure. NULL means */
                                    /* Allocate/init new, non-NULL   */
                                    /* means init existing structure */
{
    ALIGN(16) unsigned char tmp[16] = {0,};
    ALIGN(16) __m128i tmp_2 = _mm_setzero_si128();
    ALIGN(16) __m128i enc_key[11];
    
    unsigned first_bit, last_bit, i;

        /* Initialize AES keys.   (Note that if one is only going to 
           encrypt, key->rdk can be eliminated */
        AES_128_Key_Expansion(K_1, enc_key);

        AES_encrypt(  tmp_2, (__m128i*)&tmp[0], enc_key, 10);
        /* Precompute L[i]-values. L[0] is synonym of L */

        for (i = 0; i <= PRE_COMP_BLOCKS; i++) {

            memcpy(&L[i], tmp, 16);   /* Copy tmp to L[i] */
            first_bit = tmp[0] & 0x80u;    /* and multiply tmp by x */
            shift_left(tmp);
            if (first_bit) 
                tmp[15] ^= 0x87;
            
        }

        /* Precompute L_inv = L . x^{-1} */
        memcpy(tmp, (unsigned char*)&L[0], 16);
        last_bit = tmp[15] & 0x01;
        shift_right(tmp);

        if (last_bit) {
            tmp[0] ^= 0x80;
            tmp[15] ^= 0x43;
        }
        memcpy(&L_inv, tmp, 16);

        /* Set tag length used for this session */
}
    


/************************************************************************* 
 * shift_left  
 *************************************************************************/
static void
shift_left(unsigned char *x)
/* 128-bit shift-left by 1 bit: *x <<= 1.                                */
{
    int i;
    for (i = 0; i < 15; i++) {
        x[i] = (x[i] << 1) | (x[i+1] & 0x80 ? 1 : 0);
    }
    x[15] = (x[15] << 1);
}

/************************************************************************* 
 * shift_right 
 *************************************************************************/
static void
shift_right(unsigned char *x)
/* 128-bit shift-right by 1 bit:  *x >>= 1                               */
{
    int i;
    for (i = 15; i > 0; i--) {
        x[i] = (x[i] >> 1) | (x[i-1] & 1 ? 0x80u : 0);
    }
    x[0] = (x[0] >> 1);
}



static inline __m128i double_block(__m128i bl) {
		const __m128i mask = _mm_set_epi32(135,1,1,1);
		__m128i tmp = _mm_srai_epi32(bl, 31);
        tmp = _mm_and_si128(tmp, mask);
        bl = _mm_slli_epi32(bl, 1);
		return _mm_xor_si128(bl,tmp);
	}