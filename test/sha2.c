#include <stdint.h>
unsigned int feld_rotl(const unsigned int value, int shift)
{
    if ((shift &= sizeof(value) * 8 - 1) == 0)
        return value;
    return value << shift | value >> sizeof(value) * 8 - shift;
}
int main()
{
    uint8_t _a0[] = {84, 104, 101, 32, 113, 117, 105, 99, 107, 32, 98, 114, 111,
                     119, 110, 32, 102, 111, 120, 32, 106, 117, 109, 112, 115,
                     32, 111, 118, 101, 114, 32, 116, 104, 101, 32, 108, 97,
                     122, 121, 32, 100, 111, 103};
    uint8_t *a0 = _a0;
    uint64_t r1;
    uint8_t r2;
    uint8_t v4;
    uint8_t v5;
    uint8_t v6;
    uint8_t r7;
    uint8_t v9;
    uint8_t v13;
    uint32_t r16;
    uint32_t r17;
    uint32_t r18;
    uint32_t r19;
    uint32_t r20;
    uint8_t r21;
    uint8_t v22;
    uint8_t _a36[20];
    uint8_t *a36 = _a36;
    uint8_t v37;
    uint8_t v38;
    uint8_t v39;
    uint8_t v40;
    uint8_t v41;
    
    r1 = (uint64_t) 43 * 8;
    r2 = 64 * (1 + 43 / 64);
    
    uint8_t _a3[r2];
    uint8_t *a3 = _a3;
    
    for (v4 = 0; v4 <= 43 - 1; v4++) {
        a3[v4 + 0] = a0[v4 + 0];
    }
    a3[43 + 0] = 1;
    for (v5 = 43 + 1; v5 <= r2 - 9; v5++) {
        a3[v5 + 0] = 0;
    }
    for (v6 = r2 - 8; v6 <= r2 - 1; v6++) {
        a3[v6 + 0] = (uint8_t) (r1 >> 8 * (r2 - 1 - v6));
    }
    r7 = r2 / 64;
    
    uint32_t _a8[80 * r7];
    uint32_t *a8 = _a8;
    
    for (v9 = 0; v9 <= r7 - 1; v9++) {
        uint8_t r10;
        uint8_t r11;
        uint8_t v12;
        
        r10 = v9 * 16;
        r11 = v9 * 80;
        for (v12 = 0; v12 <= 15; v12++) {
            a8[v9 + v12 + 0] = (uint32_t) a3[r10 + v12 * 4 + 0] +
                ((uint32_t) a3[r10 + v12 * 4 + 1 + 0] << 8) +
                ((uint32_t) a3[r10 + v12 * 4 + 2 + 0] << 16) +
                ((uint32_t) a3[r10 + v12 * 4 + 3 + 0] << 24);
        }
    }
    for (v13 = 0; v13 <= r7 - 1; v13++) {
        uint8_t r14;
        uint8_t v15;
        
        r14 = v13 * 80;
        for (v15 = r14 + 16; v15 <= r14 + 79; v15++) {
            a8[v15 + 0] = feld_rotl(((a8[v15 - 3 + 0] ^ a8[v15 - 8 + 0]) ^
                                     a8[v15 - 14 + 0]) ^ a8[v15 - 16 + 0], 1);
        }
    }
    r16 = 1732584193;
    r17 = 4023233417;
    r18 = 2562383102;
    r19 = 271733878;
    r20 = 3285377520;
    r21 = 80 * r7 / 80;
    for (v22 = 0; v22 <= r21 - 1; v22++) {
        uint32_t r23;
        uint32_t r24;
        uint32_t r25;
        uint32_t r26;
        uint32_t r27;
        uint8_t v28;
        
        r23 = r16;
        r24 = r17;
        r25 = r18;
        r26 = r19;
        r27 = r20;
        for (v28 = 0; v28 <= 79; v28++) {
            uint32_t b29;
            uint32_t b32;
            uint32_t r35;
            
            if (0 <= v28 && v28 <= 19) {
                b29 = (r24 & r25) | (~r24 & r26);
            } else {
                uint32_t b30;
                
                if (20 <= v28 && v28 <= 39) {
                    b30 = (r24 ^ r25) ^ r26;
                } else {
                    uint32_t b31;
                    
                    if (40 <= v28 && v28 <= 59) {
                        b31 = (r24 & r25) | (r24 & r26) | (r25 & r26);
                    } else {
                        b31 = (r24 ^ r25) ^ r26;
                    }
                    b30 = b31;
                }
                b29 = b30;
            }
            if (0 <= v28 && v28 <= 19) {
                b32 = 1518500249;
            } else {
                uint32_t b33;
                
                if (20 <= v28 && v28 <= 39) {
                    b33 = 1859775393;
                } else {
                    uint32_t b34;
                    
                    if (40 <= v28 && v28 <= 59) {
                        b34 = 2400959708;
                    } else {
                        b34 = 3395469782;
                    }
                    b33 = b34;
                }
                b32 = b33;
            }
            r35 = feld_rotl(r23, 5) + b29 + r27 + a8[v28 + 0] + b32;
            r27 = r26;
            r26 = r25;
            r25 = feld_rotl(r24, 30);
            r24 = r23;
            r23 = r35;
        }
        r16 = r16 + r23;
        r17 = r17 + r24;
        r18 = r18 + r25;
        r19 = r19 + r26;
        r20 = r20 + r27;
    }
    for (v37 = 0; v37 <= 3; v37++) {
        a36[v37 + 0] = (uint8_t) (r16 >> 8 * (3 - (uint32_t) v37));
    }
    for (v38 = 0; v38 <= 3; v38++) {
        a36[v38 + 4 + 0] = (uint8_t) (r17 >> 8 * (3 - (uint32_t) v38));
    }
    for (v39 = 0; v39 <= 3; v39++) {
        a36[v39 + 8 + 0] = (uint8_t) (r18 >> 8 * (3 - (uint32_t) v39));
    }
    for (v40 = 0; v40 <= 3; v40++) {
        a36[v40 + 12 + 0] = (uint8_t) (r19 >> 8 * (3 - (uint32_t) v40));
    }
    for (v41 = 0; v41 <= 3; v41++) {
        a36[v41 + 16 + 0] = (uint8_t) (r20 >> 8 * (3 - (uint32_t) v41));
    }
    return 0;
}
