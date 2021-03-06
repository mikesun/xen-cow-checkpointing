/******************************************************************************
 * string.c
 * 
 * These provide something for compiler-emitted string operations to link
 * against.
 */

#include <xen/config.h>
#include <xen/lib.h>

#undef memcpy
void *memcpy(void *dest, const void *src, size_t n)
{
    long d0, d1, d2;

    asm volatile (
#ifdef __i386__
        "   rep movsl        ; "
#else
        "   rep movsq        ; "
        "   testb $4,%b4     ; "
        "   je 0f            ; "
        "   movsl            ; "
        "0:                  ; "
#endif
        "   testb $2,%b4     ; "
        "   je 1f            ; "
        "   movsw            ; "
        "1: testb $1,%b4     ; "
        "   je 2f            ; "
        "   movsb            ; "
        "2:                    "
        : "=&c" (d0), "=&D" (d1), "=&S" (d2)
        : "0" (n/sizeof(long)), "q" (n), "1" (dest), "2" (src)
        : "memory");

    return dest;
}

#undef memset
void *memset(void *s, int c, size_t n)
{
    long d0, d1;

    asm volatile (
        "rep stosb"
        : "=&c" (d0), "=&D" (d1)
        : "a" (c), "1" (s), "0" (n)
        : "memory");

    return s;
}

#undef memmove
void *memmove(void *dest, const void *src, size_t n)
{
    long d0, d1, d2;
 
    if ( dest < src )
        return memcpy(dest, src, n);

    asm volatile (
        "   std         ; "
        "   rep movsb   ; "
        "   cld           "
        : "=&c" (d0), "=&S" (d1), "=&D" (d2)
        : "0" (n), "1" (n-1+(const char *)src), "2" (n-1+(char *)dest)
        : "memory");

    return dest;
}

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
