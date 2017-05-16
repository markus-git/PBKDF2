#include <stdint.h>
#include <string.h>

#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>

double get_time()
{
    struct timeval t;
    struct timezone tzp;
    gettimeofday(&t, &tzp);
    return t.tv_sec + t.tv_usec*1e-6;
}

unsigned int feld_rotl(const unsigned int value, int shift)
{
    if ((shift &= sizeof(value) * 8 - 1) == 0)
        return value;
    return value << shift | value >> sizeof(value) * 8 - shift;
}

uint8_t *sha1()
{
    uint8_t _a0[] = {84, 104, 101, 32, 113, 117, 105, 99, 107, 32, 98, 114, 111,
                     119, 110, 32, 102, 111, 120, 32, 106, 117, 109, 112, 115,
                     32, 111, 118, 101, 114, 32, 116, 104, 101, 32, 108, 97,
                     122, 121, 32, 100, 111, 103};
    uint8_t *a0 = _a0;
    uint64_t r1;
    uint8_t _a2[64];
    uint8_t *a2 = _a2;
    uint8_t v3;
    uint8_t v4;
    uint32_t _a5[80];
    uint32_t *a5 = _a5;
    uint8_t v6;
    uint8_t v7;
    uint32_t r8;
    uint32_t r9;
    uint32_t r10;
    uint32_t r11;
    uint32_t r12;
    uint32_t r13;
    uint32_t r14;
    uint32_t r15;
    uint32_t r16;
    uint32_t r17;
    uint8_t v18;
    uint8_t _a26[20];
    uint8_t *a26 = _a26;
    uint8_t v27;
    uint8_t v28;
    uint8_t v29;
    uint8_t v30;
    uint8_t v31;
    
    r1 = (uint64_t) 43 * 8;
    memcpy(a2, a0, 43 * sizeof(uint8_t));
    a2[43 + 0] = 1;
    for (v3 = 43 + 1; v3 <= 55; v3++) {
        a2[v3 + 0] = 0;
    }
    for (v4 = 56; v4 <= 63; v4++) {
        a2[v4 + 0] = (uint8_t) (r1 >> 8 * (63 - (uint32_t) v4));
    }
    for (v6 = 0; v6 <= 15; v6++) {
        a5[v6 + 0] = (uint32_t) a2[v6 * 4 + 0] + ((uint32_t) a2[v6 * 4 + 1 +
                                                                0] << 8) +
            ((uint32_t) a2[v6 * 4 + 2 + 0] << 16) + ((uint32_t) a2[v6 * 4 + 3 +
                                                                   0] << 24);
    }
    for (v7 = 16; v7 <= 79; v7++) {
        a5[v7 + 0] = feld_rotl(((a5[v7 - 3 + 0] ^ a5[v7 - 8 + 0]) ^ a5[v7 - 14 +
                                                                       0]) ^
                               a5[v7 - 16 + 0], 1);
    }
    r8 = 1732584193;
    r9 = 4023233417;
    r10 = 2562383102;
    r11 = 271733878;
    r12 = 3285377520;
    r13 = r8;
    r14 = r9;
    r15 = r10;
    r16 = r11;
    r17 = r12;
    for (v18 = 0; v18 <= 79; v18++) {
        uint32_t b19;
        uint32_t b22;
        uint32_t r25;
        
        if (0 <= v18 && v18 <= 19) {
            b19 = (r14 & r15) | (~r14 & r16);
        } else {
            uint32_t b20;
            
            if (20 <= v18 && v18 <= 39) {
                b20 = (r14 ^ r15) ^ r16;
            } else {
                uint32_t b21;
                
                if (40 <= v18 && v18 <= 59) {
                    b21 = (r14 & r15) | (r14 & r16) | (r15 & r16);
                } else {
                    b21 = (r14 ^ r15) ^ r16;
                }
                b20 = b21;
            }
            b19 = b20;
        }
        if (0 <= v18 && v18 <= 19) {
            b22 = 1518500249;
        } else {
            uint32_t b23;
            
            if (20 <= v18 && v18 <= 39) {
                b23 = 1859775393;
            } else {
                uint32_t b24;
                
                if (40 <= v18 && v18 <= 59) {
                    b24 = 2400959708;
                } else {
                    b24 = 3395469782;
                }
                b23 = b24;
            }
            b22 = b23;
        }
        r25 = feld_rotl(r13, 5) + b19 + r17 + a5[v18 + 0] + b22;
        r17 = r16;
        r16 = r15;
        r15 = feld_rotl(r14, 30);
        r14 = r13;
        r13 = r25;
    }
    r8 = r8 + r13;
    r9 = r9 + r14;
    r10 = r10 + r15;
    r11 = r11 + r16;
    r12 = r12 + r17;
    for (v27 = 0; v27 <= 3; v27++) {
        a26[v27 + 0] = (uint8_t) (r8 >> 8 * (3 - (uint32_t) v27));
    }
    for (v28 = 0; v28 <= 3; v28++) {
        a26[v28 + 4 + 0] = (uint8_t) (r9 >> 8 * (3 - (uint32_t) v28));
    }
    for (v29 = 0; v29 <= 3; v29++) {
        a26[v29 + 8 + 0] = (uint8_t) (r10 >> 8 * (3 - (uint32_t) v29));
    }
    for (v30 = 0; v30 <= 3; v30++) {
        a26[v30 + 12 + 0] = (uint8_t) (r11 >> 8 * (3 - (uint32_t) v30));
    }
    for (v31 = 0; v31 <= 3; v31++) {
        a26[v31 + 16 + 0] = (uint8_t) (r12 >> 8 * (3 - (uint32_t) v31));
    }
    
    return a26;
}

int main() {

    uint16_t iter;

    double before = get_time();
    for (iter = 1; iter <= 1000; iter++) {
      sha1();
    }
    double diff = get_time() - before;
    printf("%f\n", diff);

    return 0;
}
