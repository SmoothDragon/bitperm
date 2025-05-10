#!/usr/bin/env python

# _size4.pyx

import random as rand # Avoid conflict with stdlib.h

ctypedef unsigned long long ulong
ctypedef unsigned int uint

cdef extern from "Python.h":
    void* PyMem_Malloc(int)
    void  PyMem_Free(void* p)
    
cdef extern from "stdlib.h":
    int random()
    ctypedef long size_t
    void* malloc(size_t size)
    void free(void* ptr)

from size import rbin, bin

#############################################################
# BitStatic class
#############################################################

cdef class Size4:
    cdef public uint n, nn, N
    cdef public ulong one, m_identity, p_identity
    cdef public ulong m_mask, r_mask, c_mask, p_mask, p_base
    cdef ulong* x_mask
    
    def __init__(self, uint n=4):
        cdef ulong i,j
        cdef ulong id, one

        one = 1
        self.n = n
        self.nn = n*n
        self.N = 1ull << n
        
        # Define the Identity matrix
        id = 0
        for i in range(n):
            id ^= (1ull << (n+1)*i)
        self.m_identity = id
        
        # Define the Identity permutation
        id = 0
        for i in range( 1 << n ):
            id = id ^ ((i*1ull) << (n*i)) 
        self.p_identity = id

        # The matrix mask is n*n bits set to 1111..1
        self.m_mask = (1ull << n*n) - 1 
        # The row mask is the low n bits set to 111..1
        self.r_mask = (1ull << n) - 1 
        # The column mask is n 1's spaced n bits apart 
        id = 0
        for i in range(n):
            id ^= (1ull << (i*n))
        self.c_mask = id

        # The permutation mask is 2**n  1's
        self.p_mask = 2*((1ull << (self.N*self.n-1)) - 1) + 1
        self.p_base = self.p_mask // max(self.r_mask, 1)
        
        # x_mask[i] is the locations of monomials with no x_i.
        self.x_mask = <ulong*> malloc(sizeof(ulong)*self.n)
        for i in range(self.n):
            self.x_mask[i] = (self.p_mask // ((1 << (1<<(i+1)))-1) ) \
			     * ((1 << (1<<(i)))-1)

    def x_test(cls):
        for i in range(cls.n):
            print rbin(cls.x_mask[i],64)

    def p_id(cls):
        '''
        Mysterious bug
        p_id() != p_identity
        '''
        return int(cls.p_identity)

    def p_mk(cls):
        return int(cls.p_mask)

    ################################################################
    # Print methods
    ################################################################
    def str_v(cls, v):
        '''Binary form of permutation
        >>> print Size4(3).str_v(0)
        000
        >>> print Size4(3).str_v(6)
        011
        '''
        return rbin(v, cls.n)

    def str_m(cls, m):
        '''Binary form of matrix
        >>> print Size(3).str_m(0421)
        100
        010
        001
        >>> print Size(3).str_m(0153)
        110
        101
        100
        '''
        s = ''
        for i in xrange(cls.n):
            t = (m >> cls.n*i) & cls.r_mask
            s += rbin(t, cls.n) + '\n'
        s = s[:-1]
        return s

    def str_a(cls, a):
        '''Binary form of affine matrix
        >>> print Size(3).str_a(07421)
        100
        010
        001
        111
        >>> print Size(3).str_a(04153)
        110
        101
        100
        001
        '''
        s = ''
        for i in xrange(cls.n + 1):
            t = (a >> cls.n*i) & cls.r_mask
            s += rbin(t, cls.n) + '\n'
        s = s[:-1]
        return s

    def str_p(cls, p):
        '''Binary form of permutation
        >>> s = Size(3)
        >>> print s.str_p(s.p_identity)
        0 1 2 3 4 5 6 7
        >>> print s.str_p(067452301)
        1 0 3 2 5 4 7 6
        '''
        s = str(p & cls.r_mask)
        for i in xrange(1, cls.N):
            s += ' '+str((p >> (i*cls.n)) & cls.r_mask)
        return s

    def str_t(cls, p):
        '''Binary form of permutation
        >>> s = Size(3)
        >>> print s.str_t(s.p_identity),
        000
        001
        010
        011
        100
        101
        110
        111
        >>> print s.str_t(067452301),
        001
        000
        011
        010
        101
        100
        111
        110
        '''
        s = ''
        for i in xrange(cls.N):
            s += bin((p >> (i*cls.n)) & cls.r_mask, cls.n)+'\n'
        return s

    ################################################################
    # Conversion methods
    ################################################################
    '''
    NOTE: Finite Functions acting on [0,1,...,2**n-1]
    0 1 2
    3 4 5 ==> 8 7 6 5 4 3 2 1 0
    6 7 8

    Functions are named as follows
    _ReturnType_InputTypes_FunctionDescription
    Possible types are:
    m matrix
    v vector
    r row vector
    c column vector
    a affine
    b bit
    p permutation
    ? controlled affine (condition off of most significant bits)
    '''

    cpdef ulong r_c(cls, ulong c):
        '''Converts column vector to row vector
        >>> s = Size(3)
        >>> print s.str_v(s.r_c(s.c_mask))
        111
        '''
        c ^= c >> (2*cls.n-2)
        c ^= (c & (cls.r_mask << cls.n)) >> (cls.n - 1)
        c &= cls.r_mask
        return c

    cpdef ulong c_r(cls, ulong r):
        '''Converts row vector to column vector
        >>> s = Size(3)
        >>> print s.str_v(s.r_c(s.c_r(s.r_mask)))
        111
        '''
        r ^= (r >> 1) << cls.n
        r ^= (r >> 2) << 2*cls.n
        r &= cls.c_mask
        return r

    cpdef ulong p_v(cls, ulong v):
        '''Returns permutation equal to adding vector v.
        >>> s = Size(3)
        >>> print s.str_p(s.p_v(1))
        1 0 3 2 5 4 7 6
        '''
        return cls.p_identity ^ (v * cls.p_base)

    cpdef ulong p_m(cls, ulong m):
        '''Returns permutation equal to matrix multiplication by m.
        >>> print Size(3).str_p(Size(3).p_m(0153))
        0 3 5 6 1 2 4 7
        '''
        cdef uint i
        cdef ulong p
        p = 0
        for i in range(cls.N):
            p ^= cls.r_rm_mul(i, m) << (i * cls.n)
        return p

    cpdef ulong p_a(cls, ulong a):
        '''Permutation equal to affine matrix multiplication by a.
        >>> print Size(3).str_p(Size(3).p_a(04153))
        4 7 1 2 5 6 0 3
        '''
        cdef ulong p, i
        p = 0
        for i in range(cls.N):
            p ^= cls.r_ra_mul(i, a) << (i * cls.n)
        return p

    cpdef ulong a_v(cls, ulong v):
        '''Returns affine matrix equal to adding vector v.
        >>> print Size(3).str_a(Size(3).a_v(6))
        100
        010
        001
        011
        '''
        return cls.m_identity ^ (v << cls.nn)

    cpdef ulong m_v(cls, ulong v):
        '''Return matrix with char polynomial associated with v.
        >>> print Size(3).str_m(Size(3).m_v(3))
        010
        001
        110
        '''
        cdef ulong m
        m = cls.m_identity << 1
        m ^= ( v << (cls.n - 1) * cls.n ) & cls.m_mask
        return m

    def a_m(cls, m):
        return m

    # TODO: Tensor two permutations together


    ################################################################
    # Coercion methods
    ################################################################
    cpdef ulong v_p(cls, ulong p):
        '''Returns zero shift of permutation.
        Coerce - Inverts p_v
        >>> s = Size(3)
        >>> print  s.str_v(s.v_p(s.p_identity))
        000
        '''
        return p & cls.r_mask

    cpdef ulong m_p(cls, ulong p):
        '''Matrix function of permutation basis.
        Coerce - Inverts p_m
        >>> s = Size(3)
        >>> print  s.str_m(s.m_p(s.p_identity))
        100
        010
        001
        '''
        cdef uint i
        m = 0
        for i in range(cls.n):
            m ^= (p >> ( (1 << i) * cls.n) & cls.r_mask) \
		 << (i * cls.n)
        return m

    cpdef ulong a_p(cls, ulong p):
        '''Returns affine function of permutation basis.
        Coerce - Inverts p_a
        >>> s = Size(3)
        >>> print  s.str_a(s.a_p(s.p_identity))
        100
        010
        001
        000
        >>> print  s.str_a(s.a_p(067452301))
        100
        010
        001
        100
        '''
        cdef uint i
        cdef ulong v, a
        a = 0
        v = p & cls.r_mask
        for i in range(cls.n):
            a ^= (v ^ (p >> ( (1 << i) * cls.n) & cls.r_mask)) \
		 << (i * cls.n)
        return a ^ (v << cls.nn)

    cpdef ulong v_a(cls, ulong a):
        '''Returns affine shift.
        Coerce - Inverts a_v
        >>> s = Size(3)
        >>> print  s.str_v(s.v_a(07421))
        111
        '''
        return (a >> cls.nn) & cls.r_mask

    cpdef ulong m_a(cls, ulong a):
        '''Returns zero shift of permutation.
        Coerce - Inverts convert.a_m
        >>> s = Size(3)
        >>> print  s.str_m(s.m_a(07421))
        100
        010
        001
        '''
        return a & cls.m_mask

    ################################################################
    # Get and set methods
    ################################################################

    cpdef ulong r_pi_get(cls, ulong p, uint index):
        '''Returns the value p(i) from the permutation p.
        >>> s = Size(3)
        >>> print s.str_v(s.r_pi_get(s.p_identity, 4))
        001
        '''
        return (p >> cls.n*index) & cls.r_mask

    cpdef ulong b_vi_get(cls, ulong v, uint index):
        '''
        Candidate static method.
        '''
        return (v >> index) & 1

    cpdef ulong b_mij_get(cls, ulong m, uint i, uint j):
        '''Returns the (i,j) entry of the matrix m.
        >>> s = Size(3)
        >>> print s.b_mij_get(s.m_identity,0,0)
        1
        >>> print s.b_mij_get(s.m_identity,1,0)
        0
        '''
        return (m >> (i*cls.n +j)) & 1

    '''
    _b_ci_get
    _r_mi_get
    _c_mi_get
    _vib_set
    '''

    ################################################################
    # Matrix methods
    ################################################################

    cpdef ulong r_rm_mul(cls, ulong r, ulong m):
        '''Row vector times matrix
        >>> s = Size(3)
        >>> print s.str_v(s.r_rm_mul(1, 0421))
        100
        >>> print s.str_v(s.r_rm_mul(7, 0437))
        000
        >>> print s.str_v(s.r_rm_mul(7, 0467))
        101
        '''
        cdef ulong v
        v = cls.c_r(r)
        m &= v * cls.r_mask
        return cls.r_m_xor_cols(m)

    cpdef ulong r_ra_mul(cls, ulong r, ulong a):
        '''Row vector times affine matrix
        >>> s = Size(3)
        >>> print s.str_v(s.r_ra_mul(1, 03421))
        010
        >>> print s.str_v(s.r_ra_mul(7, 05437))
        101
        >>> print s.str_v(s.r_ra_mul(7, 01467))
        001
        '''
        cdef ulong v,m
        v = cls.c_r(r)
        m = a & (v * cls.r_mask)
        return cls.r_m_xor_cols(m) ^ (a >> cls.nn)

    cpdef ulong r_mr_mul(cls, ulong m, ulong r):
        '''Matrix vector times row
        >>> s = Size(3)
        >>> print s.str_v(s.r_mr_mul(0421, 1))
        100
        >>> print s.str_v(s.r_mr_mul(0665, 7))
        000
        >>> print s.str_v(s.r_mr_mul(0467, 7))
        101
        '''
        cdef ulong v
        m &= r * cls.c_mask
        v = cls.c_m_xor_rows(m)
        return cls.r_c(v)

    cpdef ulong r_ar_mul(cls, ulong a, ulong r):
        '''Affine matrix times row vecto
        First multiply by matrix and then add affine component
        >>> print Size(3).str_v(Size(3).r_ar_mul(04421, 1))
        101
        >>> print Size(3).str_v(Size(3).r_ar_mul(07566, 1))
        110
        '''
        cdef ulong m, v
        m = a & (r * cls.c_mask) & cls.m_mask
        v = cls.c_m_xor_rows(m)
        return cls.r_c(v) ^ (a >> cls.nn)

    cpdef ulong m_mm_mul(cls, ulong m1, ulong m2):
        '''Matrix multiplication
        >>> s = Size(3)
        >>> print s.str_m(s.m_mm_mul(0421, 0421))
        100
        010
        001

        >>> print s.str_m(s.m_mm_mul(311, 311))
        101
        010
        001
        '''
        cdef uint i
        cdef ulong f,r,t
        t = cls.m_m_transpose(m2)
        r = cls.c_m_xor_rows(m1 & t)
        for i in range(1, cls.n):
            f = cls.m_mi_upshift_rows(m1, i)
            f = cls.c_m_xor_rows(f & t)
            f = cls.m_mi_upshift_rows(f, cls.n - i)
            r ^= f << (cls.n - i)
        r = cls.m_m_ishift_rows(r)
        return r

    cpdef ulong a_aa_mul(cls, ulong a1, ulong a2):
        '''Affine Matrix multiplication        
        >>> print Size(3).str_a(Size(3).a_aa_mul(0421, 0421))
        100
        010
        001
        000
        >>> print Size(3).str_a(Size(3).a_aa_mul(07467, 07467))
        101
        010
        001
        010
        '''
        cdef ulong m,v
        m = cls.m_mm_mul(a1 & cls.m_mask, a2 & cls.m_mask)
        v = cls.r_ra_mul((a1 >> cls.nn) & cls.r_mask, a2)
        return m ^ (v << cls.nn)


    cpdef ulong m_m_inv(cls, ulong m):
        '''Assuming the matrix is invertible. Returns the inverse.
        >>> s = Size(3)
        >>> print s.str_m(s.m_m_inv(0421))
        100
        010
        001
        >>> print s.str_m(s.m_m_inv(143))
        010
        001
        111
        >>> print s.str_m(s.m_m_inv(0124))
        001
        010
        100
        >>> print Size(2).str_m(Size(2).m_m_inv(6))
        01
        10
        '''
        cdef ulong m1,m2,sval,oval,val
        cdef uint i,j
        m1 = m
        m2 = cls.m_identity
        for i in range(cls.n):
            for j in range(i, cls.n): # pivot a 1 to (i,i) position
                if cls.b_mij_get(m1, j, i) == 1:
                    break
            m1 = cls.m_mij_swap_rows(m1, i, j)
            m2 = cls.m_mij_swap_rows(m2, i, j)
            val = (m1 >> i) & cls.c_mask # which rows added
            val ^= 1ull << i*cls.n # zero out pivot position
            sval = val * ((m1 >> i*cls.n) & cls.r_mask)
            oval = val * ((m2 >> i*cls.n) & cls.r_mask)
            m1 ^= sval
            m2 ^= oval
        return m2

    cpdef ulong a_a_inv(cls, ulong a):
        '''Affine inverse. Assume multiplication on right.
        >>> Size4(3).a_a_inv(07567)
        1003L
        '''
        cdef ulong m,v
        m = cls.m_m_inv(a & cls.m_mask)
        v = cls.r_rm_mul(a >> cls.nn, m)
        return m ^ (v << cls.nn)

    cpdef ulong m_m_transpose(cls, ulong m):
        '''Transpose of Bit Matrix
        >>> Size(3).m_m_transpose(0421)
        273
        >>> Size(3).m_m_transpose(0153)
        143
        '''
        cdef ulong f
        cdef uint i
        f = 0
        for i in range(cls.n):
            t = cls.c_mask & (m >> i)
            f ^= cls.r_c(t) << (cls.n * i)
        return f

    def m_random(cls):
        '''Returns a random invertible bit matrix
        >>> s = Size(3); m=s.m_random();
        >>> s.m_mm_mul(m, s.m_m_inv(m)) == s.identity
        True
        '''
        while True:
            n = rand.randrange(1<<cls.nn)
            if cls.is_inv_a(n):
                return n

    def a_random(cls):
        '''Returns a random invertible affine bit matrix
        >>> s = Size(3); a=s.a_random();
        >>> s.a_aa_mul(a, s.a_a_inv(a)) == s.identity
        True
        '''
        while True:
            n = rand.randrange(1<<cls.nn)
            if cls.is_inv_a(n):
                return n ^ (rand.randrange(cls.N) << cls.nn)


    ################################################################
    # Generator methods
    ################################################################

    """
    def density2(cls):
        '''Generate all weight 2 words.
        >>> for i in Size(4).density2(): print Size(4).str_v(i)
        1100
        1010
        1001
        0110
        0101
        0011
        '''
        m = 3
        for i in xrange(cls.n-1):
            current = (m << i)
            yield current
            for j in xrange(i+1, cls.n-1):
                current ^= m << j
                yield current
        return

    def density3(cls):
        '''Generate all weight 2 words.
        >>> for i in Size(5).density3(): print Size(5).str_v(i)
        11100
        11010
        11001
        10110
        10101
        10011
        01110
        01101
        01011
        00111
        '''
        m = 7
        for i in xrange(cls.n-2):
            last = (m << i)
            current = last
            yield current
            for j in xrange(i+1, cls.n-2):
                for k in xrange(j+1, cls.n-1):
                    current ^= 3 << k
                    yield current
                last ^= 5 << j
                current = last
                yield current
        return
    """

    ################################################################
    # Helper methods
    ################################################################

    cpdef ulong r_m_xor_cols(cls, ulong m):
        '''XOR the values in each column to form a row vector.
        >>> s = Size(3)
        >>> s.r_m_xor_cols(s.m_identity) == s.r_mask
        True
        '''
        cdef uint i
        for i in range(1, cls.n):
            m ^= (m >> (cls.n * i) ) & cls.r_mask
        m &= cls.r_mask
        return m

    cpdef ulong c_m_xor_rows(cls, ulong m):
        '''XOR the values in each row to form a column vector.
        >>> s = Size(3)
        >>> s.c_m_xor_rows(s.m_identity) == s.c_mask
        True
        '''
        cdef uint i
        for i in range(1, cls.n):
            m ^= (m >> i) & cls.c_mask
        m &= cls.c_mask
        return m

    cpdef ulong m_mij_swap_rows(cls, ulong m, uint i, uint j):
        '''
        >>> Size(3).m_mij_swap_rows(0421, 0, 2)
        84
        '''
        cdef ulong val
        val = (m >> cls.n*i) ^ (m >> cls.n*j)
        val &= cls.r_mask
        m ^= val << cls.n*i
        m ^= val << cls.n*j
        return m

    cpdef ulong m_mi_upshift_rows(cls, ulong m, int i):
        ''' Circular shift of rows upward
        >>> Size(3).m_mi_upshift_rows(0421, 1)
        98
        '''
        return (m>>cls.n*i)^((m<<(cls.n*(cls.n-i)))&cls.m_mask)


    cpdef ulong m_m_ishift_rows(cls, ulong m):
        ''' Circular shift ith row by i
        >>> Size(3).m_m_ishift_rows(0421)
        161
        '''
        cdef uint i
        cdef ulong f
        f = m & cls.r_mask
        for i in range(1, cls.n):
            val = (m >> cls.n*i) & cls.r_mask
            val = cls.r_r_circ_shift(val, i)
            f ^= val << cls.n*i
        return f

    cpdef ulong r_r_circ_shift(cls, ulong r, uint i):
        return ((r>>(cls.n-i)&cls.r_mask)^(r<<(i)))&cls.r_mask

    cpdef ulong m_rr_outer_product(cls, ulong r1, ulong r2):
        ''' Outer product
        >>> s = Size(3)
        >>> print s.str_m(s.m_rr_outer_product(05, 07))
        111
        000
        111
        '''
        r1 = cls.c_r(r1)
        return r1 * r2

    '''
    m_m_canonical form
    b_vv_dotproduct
    '''


    ################################################################
    # Permutation methods
    ################################################################

    cpdef ulong p_p_inv(cls, ulong p):
        '''Assuming the function is a permutation. Returns inverse.
        >>> print Size(3).str_p(Size(3).p_p_inv(024710536))
        3 4 7 1 6 2 0 5
        '''
        cdef ulong i
        cdef ulong f
        f = 0
        for i in range(cls.N):
            f ^= i << ( ( (p >> i*cls.n) & cls.r_mask ) * cls.n )
        return f

    cpdef ulong p_p_reverse(cls, ulong p):
        '''Reverses permuation as a list
        >>> print Size(3).str_p(Size(3).p_p_reverse(024710536))
        2 4 7 1 0 5 3 6
        '''
        cdef uint i
        cdef ulong f
        f = 0
        for i in range(cls.N):
            f ^= ((p>>i*cls.n)&cls.r_mask)<<(cls.N-i-1)*cls.n
        return f
    
    cpdef ulong p_pp_mul(cls, ulong p0, ulong p1):
        '''Composition function.
        >>> print Size(3).str_p(Size(3).p_pp_mul(024710536,024710536))
        4 0 7 6 3 2 1 5
        >>> print Size(3).str_p(Size(3).p_pp_mul(024710536,053610742))
        3 0 6 2 4 5 1 7
        '''
        cdef uint i
        cdef ulong f, p0i, p1j
        f = 0
        for i in range(cls.N):
            p0i = (p0 >> i*cls.n) & cls.r_mask
            p1j = (p1 >> p0i*cls.n) & cls.r_mask
            f ^= p1j << cls.n*i
        return f
    
    cpdef ulong p_pa_mul(cls, ulong p, ulong a):
        '''Composition function.
        >>> s = Size(3)
        >>> print s.str_p(s.p_pa_mul(053610742,07124))
        5 6 0 7 3 4 1 2
        '''
        cdef uint i
        cdef ulong f, pi
        f = 0
        for i in range(cls.N):
            pi = (p >> i*cls.n) & cls.r_mask
            f ^= cls.r_ra_mul(pi, a) << cls.n*i
        return f

    cpdef ulong p_ap_mul(cls, ulong a, ulong p):
        '''Composition function. (Slower than reversed composition)
        >>> s = Size(3)
        >>> print s.str_p(s.p_ap_mul(07124,053610742))
        5 0 6 4 3 7 1 2
        '''
        pa = cls.p_a(a)
        return cls.p_pp_mul(pa,p)

    cpdef ulong p_p_fixBasis(cls, ulong p):
        cdef ulong a
        while not cls.is_inv_a(cls.a_p(p)):
            p = cls.p_ap_mul(cls.a_random(), p)
        a = cls.a_a_inv(cls.a_p(p))
        p = cls.p_pa_mul(p,a)
        return p

    cpdef uint is_a_pp_mul(cls, ulong p, ulong q):
        cdef ulong v000,v001,v010,v100,v101,v110,v111
        cdef ulong t
        v000 = (q >> (cls.n * (p&cls.r_mask)))
        v001 = (q >> (cls.n * ((p >> cls.n) & cls.r_mask)))
        v010 = (q >> (cls.n * ((p >> 2*cls.n) & cls.r_mask)))
        v011 = (q >> (cls.n * ((p >> 3*cls.n) & cls.r_mask)))
        if ((v000 ^ v001 ^ v010 ^ v011) & cls.r_mask) != 0: 
            return 0
        v100 = (q >> (cls.n * ((p >> 4*cls.n) & cls.r_mask)))
        v101 = (q >> (cls.n * ((p >> 5*cls.n) & cls.r_mask)))
        if ((v000 ^ v001 ^ v100 ^ v101) & cls.r_mask) != 0: 
            return 0
        v110 = (q >> (cls.n * ((p >> 6*cls.n) & cls.r_mask)))
        if ((v000 ^ v010 ^ v100 ^ v110) & cls.r_mask) != 0: 
            return 0
        v111 = (q >> (cls.n * ((p >> 7*cls.n) & cls.r_mask)))
        if ((v000 ^ v001 ^ v110 ^ v111) & cls.r_mask) != 0: 
            return 0
        t = cls.p_pp_mul(p,q)
        if cls.is_a_p(t) == 1: # Just test the darn thing then!
            return t
        else:
            return 0


    cpdef uint is_inv_a(cls, ulong a):
        '''Determines whether affine transformation is invertible.
        >>> Size(3).is_inv_a(02743)
        False
        >>> Size(3).is_inv_a(07764)
        True
        '''
        ai = cls.a_a_inv(a)
        return cls.a_aa_mul(a,ai) == cls.m_identity

    cpdef int cmp_p(cls, ulong p0, ulong p1):
        '''Compare using lexicographic value
        Examples:
        >>> Size(2).cmp_p(0xe4,0xd9)
        True
        '''
        cdef uint i
        cdef ulong val0, val1
        for i in range(cls.N):
            val0 = cls.r_pi_get(p0, i)
            val1 = cls.r_pi_get(p1, i)
            if val0 == val1:
                continue
            else:
                return val0 < val1
        return 0

    cpdef ulong p_random_s(cls):
        cdef ulong p
        cdef ulong i,j        
        p = cls.p_identity
        for i in range(cls.N):
            j = rand.randrange(i,cls.N)
            p = cls.p_pij_swap(p,i,j)
        return p

    cpdef ulong p_random(cls):
        cdef ulong p
        cdef ulong i,j        
        p = cls.p_identity
        for i in range(cls.N):
            j = (random() % (cls.N - i)) + i
            p = cls.p_pij_swap(p,i,j)
        return p

    cpdef ulong p_pij_swap(cls, ulong p, uint i, uint j):
        cdef ulong val
        val = cls.r_pi_get(p,i) ^ cls.r_pi_get(p,j)
        p ^= val << cls.n*i
        p ^= val << cls.n*j
        return p

    cpdef ulong p_p_next(cls, ulong p):
        cdef uint i,j
        cdef ulong pi,pj

        i = cls.N - 1
        pj = cls.r_pi_get(p,i)

        while True:
            i = i -1
            if i < 0:
                return 0
            pi = cls.r_pi_get(p, i)
            if pi < pj:
                break
            pj = pi

        j = cls.N
        while cls.r_pi_get(p, j-1) <= pi:
            j = j - 1

        p = cls.p_pij_swap(p,i,j-1)
        i = i + 1
        j = cls.N -1

        while i<j:
            p = cls.p_pij_swap(p,i,j)
            i += 1
            j -= 1
        return p

    cpdef ulong p_p_not(cls, ulong p, ulong target):
        '''NOT Gate
        >>> s = Size(3); p = s.p_identity
        >>> print s.str_p(s.p_p_cnot(p,0))
        1 0 3 2 5 4 7 6
        '''
        return p ^ (cls.p_base << target)

    cpdef ulong p_p_cnot(cls, ulong p, ulong source, ulong target):
        '''Control NOT
        >>> s = Size(3); p = s.p_identity
        >>> print s.str_p(s.p_p_cnot(p,0,1))
        0 3 2 1 4 7 6 5
        '''
        cdef ulong d
        d = (p & (cls.p_base << source)) >> source
        return p ^ (d << target)

    cpdef ulong p_p_ccnot(cls, ulong p, ulong source1, \
                          ulong source2, ulong target):
        '''Double control NOT
        >>> s = Size(3); p = s.p_identity
        >>> print s.str_p(s.p_p_ccnot(p,0,1,2))
        0 3 2 1 4 7 6 5
        '''
        cdef ulong d
        d = (p & (cls.p_base << source1)) >> source1
        d &= (p & (cls.p_base << source2)) >> source2
        return p ^ (d << target)

    cpdef ulong p_p_cccnot(cls, ulong p, ulong source1, \
                 ulong source2, ulong source3, ulong target):
        '''Triple control NOT
        >>> s = Size(4); p = s.p_identity
        >>> print s.str_p(s.p_p_cccnot(p,0,1,2,3))
        '''
        cdef ulong d
        d = (p & (cls.p_base << source1)) >> source1
        d &= (p & (cls.p_base << source2)) >> source2
        d &= (p & (cls.p_base << source3)) >> source3
        return p ^ (d << target)

    def Test3(cls, p):
        L = []
        L.append(cls.p_identity)
        L.append(cls.p_p_ccnot(L[0],0,1,2))
        L.append(cls.p_p_ccnot(L[1],0,2,1))
        L.append(cls.p_p_ccnot(L[2],1,2,0))

        for i in range(4):
            if cls.DC(p,L[i]):
                return i
        return 'Fail'

    def Test4(cls,p):
        if cls.b_p_parity(p) == 0:
            return 'Even: '+str(cls.Test4Even(p))
        else:
            return 'Odd:  '+str(cls.Test4Odd(p))

    def order(cls, p):
        '''Find order of permutation
        >>> s=Size(3); s.order(s.p_identity) == 1
        True
        >>> s.order(057136420)
        7
        '''
        d = p
        i = 1
        while True:
            if d == cls.p_identity:
                return i
            d = cls.p_pp_mul(d,p)
            i += 1
            if i > 999:
                return None
        
    ################################################################
    # Rank Algorithms
    ################################################################

    cpdef uint b_p_parity(cls, ulong p):
        '''Return the parity of the permutation.
        >>> s = Size(4); p = s.p_identity
        >>> s.b_p_parity(p)
        0
        >>> p = s.p_random(); s.b_p_parity(s.p_pp_mul(p,p))
        0
        >>> print Size(3).b_p_parity(067543210) # Toffoli Gate
        1
        '''
        cdef uint a,c,i,j
        a = 0; c = 0
        for j in range(cls.N):
            if (a>>j)&1 == 0: 
                c ^= 1
                i = j
                while True:
                    a ^= 1<<i
                    i = cls.r_pi_get(p,i)
                    if i == j:
                        break
        return c # (cls.N-c)%2


    cpdef uint n_p_lowbit(cls, ulong p):
        cdef uint n
        n = 0
        if (p & 0xffffffff) == 0:
            n += 32
            p = p >> 32
        if (p & 0xffff) == 0:
            n += 16
            p = p >> 16
        if (p & 0xff) == 0:
            n += 8
            p = p >> 8
        if (p & 0xf) == 0:
            n += 4
            p = p >> 4
        if (p & 0x3) == 0:
            n += 2
            p = p >> 2
        if (p & 0x1) == 0:
            n += 1
        return n

    cpdef uint is_a_p(cls, ulong p):
        '''Determines whether a permutation is an affine function.
        >>> print Size(3).is_a_p(Size(3).p_identity)
        True
        >>> print Size(3).is_a_p(067543210) # Toffoli Gate
        False
        >>> print Size(3).is_a_p(067452301) # NOT Gate on lsb
        True
        '''
        cdef uint i
        cdef ulong a,v
        a = 0
        v = p & cls.r_mask
        for i in range(cls.n):
            a ^= (v ^ (p >> ( (1 << i) * cls.n) & cls.r_mask)) \
		 << (i * cls.n)
        a ^= (v << cls.nn)
        for i in range(cls.N):
            if cls.r_ra_mul(i,a)!=((p>>(i*cls.n))&cls.r_mask):
                return 0
        return 1

    cpdef uint is_a_p4(cls, ulong p):
        '''Determines whether a permutation is an affine function.
        >>> print Size(4).is_a_p(Size(4).p_identity)
        True
        >>> print Size(3).is_a_p(067543210) # Toffoli Gate
        False
        >>> print Size(3).is_a_p(067452301) # NOT Gate on lsb
        True
        '''
        p ^= ( p        & 0xf)*0x1111111111111111ull
        p ^= ((p >>  4) & 0xf)*0x1010101010101010ull
        p ^= ((p >>  8) & 0xf)*0x1100110011001100ull
        if (p & 0xffff) != 0:
            return 0
        p ^= ((p >> 16) & 0xf)*0x1111000011110000ull
        if (p & 0xffffffff) != 0:
            return 0
        p ^= ((p >> 32) & 0xf)*0x1111111100000000ull
        return (p == 0)

    cpdef uint is_t_p(cls, ulong p):
        '''Determines whether a permutation is a.e. to Toffoli.
        '''
        cdef uint i
        cdef ulong t,q
        i = cls.n_p_signature(p)
        if i == 11:
            return 1
        else:
            return 0
        
    cpdef uint is_t3_p(cls, ulong p):
        '''Determines whether a permutation is a.e. to Toffoli.
        '''
        cdef uint i
        cdef ulong t,q
        i = cls.n_p_signature(p)
        if i == 3:
            return 1
        else:
            return 0
        
    cpdef uint n_p_rank(cls, ulong p):
        '''Determines rank of the four vector truth tables.
        '''
        cdef uint rank, n, a, b
        rank = 0
        while p != 0:
            n = cls.n_p_lowbit(p)
            b = n & 0x3
            a = n - b
            p ^= ((p>>b)&0x1111111111111111ull)*((p>>a)&0xf)
            rank += 1
        return rank

    cpdef ulong p_p_reduce_affine(cls, ulong p):
        p ^= ( p        & 0xf)*0x1111111111111111ull
        p ^= ((p >>  4) & 0xf)*0x1010101010101010ull
        p ^= ((p >>  8) & 0xf)*0x1100110011001100ull
        p ^= ((p >> 16) & 0xf)*0x1111000011110000ull
        p ^= ((p >> 32) & 0xf)*0x1111111100000000ull
        return p

    cpdef ulong p_p_reduce_quadratic(cls, ulong p):
        p ^= ((p >>  3*4) & 0xf)*0x1000100010001000ull
        p ^= ((p >>  5*4) & 0xf)*0x1010000010100000ull
        p ^= ((p >>  6*4) & 0xf)*0x1100000011000000ull
        p ^= ((p >>  9*4) & 0xf)*0x1010101000000000ull
        p ^= ((p >> 10*4) & 0xf)*0x1100110000000000ull
        p ^= ((p >> 12*4) & 0xf)*0x1111000000000000ull
        return p

    cpdef ulong p_p_reduce_cubic(cls, ulong p):
        p ^= ((p >>  7*4) & 0xf)*0x1000000010000000ull
        p ^= ((p >> 11*4) & 0xf)*0x1000100000000000ull
        p ^= ((p >> 13*4) & 0xf)*0x1010000000000000ull
        p ^= ((p >> 14*4) & 0xf)*0x1100000000000000ull
        return p

    def rank_signature(cls, ulong p):
        cdef uint prev, next 
        sig = [ cls.b_p_parity(p) ]
        prev = cls.n_p_rank(p)
        p = cls.p_p_reduce_affine(p)
        next = cls.n_p_rank(p)
        sig.append(prev - next)
        prev = next
        p = cls.p_p_reduce_quadratic(p)
        next = cls.n_p_rank(p)
        sig.append(prev - next)
        prev = next
        p = cls.p_p_reduce_cubic(p)
        next = cls.n_p_rank(p)
        sig.append(prev - next)
        prev = next
        return sig

    cpdef uint n_p_signature(cls, ulong p):
        cdef uint prev, next, sig 
        p = cls.p_p_reduce_affine(p)
        sig = 4 - cls.n_p_rank(p)
        p = cls.p_p_reduce_quadratic(p)
        sig ^= (4 - sig - cls.n_p_rank(p)) << 3
        return sig

    cpdef uint n_p_signature2(cls, ulong p):
        cdef uint sig 
        sig = cls.n_p_signature(p)
        sig ^= cls.DC(p,cls.p_p_inv(p)) << 6
        sig ^= cls.b_p_parity(p) << 7
        return sig

    def L_p_signature(cls, ulong p):
        '''Signature List (Linear, Quadratic, Parity,
	CommutatorSize, involution, order3, order4)
        '''
        cdef uint sig 
        sig = cls.n_p_signature(p)
        L = []
        L.append(sig&0x7)
        L.append(sig>>3)
        L.append(cls.b_p_parity(p))
        L.append(len(cls.S_p_affineCommutator(p)))
        L.append(cls.DC(p,cls.p_p_inv(p)))
        '''Order does not appear to be working
        L.append(cls.b_p_AE_Order3(p))
        L.append(cls.b_p_AE_Order4(p))
        L.append(cls.b_p_AE_Order5(p))
        L.append(cls.b_p_AE_Order6(p))
        L.append(cls.b_p_AE_Order7(p))
        L.append(cls.b_p_AE_Order8(p))
        L.append(cls.b_p_AE_Order9(p))
        L.append(cls.b_p_AE_Order16(p))
        '''
        return L


    ################################################################
    # Double Coset
    ################################################################

    cpdef uint equivDC(cls, ulong a, ulong b):
        cdef uint h
        cdef ulong t
        for h in range(1<<(cls.nn+cls.n)):
            if cls.is_inv_a(h):
                t = cls.p_pa_mul(a,h)
                t = cls.p_pp_mul(t,b)
                if cls.is_a_p_fastfail(t):
                    return 1
        return 0

    cpdef linear(cls):
        cdef ulong h
        H = set()
        for h in (1<<cls.nn):
            if cls.is_inv_a(h):
                H.add(h)
        return H

    
    ###############################################################
    # Build up a coset test
    ###############################################################


    cpdef uint DC(cls, ulong p, ulong q):
        cdef ulong* coset
        cdef ulong* qlist
        cdef ulong t
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        qlist = <ulong*> malloc(sizeof(ulong)*16)
        p = cls.p_p_inv(p)
        coset[0] = p
        p = cls.p_p_4bit_linear(p, coset+1)
        for j in range(16):
            qlist[j] = cls.p_ap_mul(cls.a_v(j),q)
        for i in range(20160):
            for j in range(16):
                #if cls.is_a_pp_mul(coset[i],qlist[j]) != 0:
                if cls.is_a_p4(cls.p_pp_mul(coset[i],qlist[j]))!=0:
                    free(coset)
                    free(qlist)
                    return 1
        free(coset)
        free(qlist)
        return 0

    cpdef ulong a_pp_DC(cls, ulong p, ulong q):
        cdef ulong* coset
        cdef ulong* qlist
        cdef ulong t, a, pi
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        qlist = <ulong*> malloc(sizeof(ulong)*16)

        pi = cls.p_p_inv(p) # pi = p^-1
        coset[0] = pi
        cls.p_p_4bit_linear(pi, coset+1)
        for j in range(16):
            qlist[j] = cls.p_ap_mul(cls.a_v(j),q)
        for i in range(20160):
            for j in range(16):
                if cls.is_a_p4(cls.p_pp_mul(coset[i],qlist[j]))!=0:
                    t = cls.p_pp_mul(coset[i],qlist[j])
                    a = cls.a_a_inv(cls.a_p(t)) << 32
                    #a = cls.a_p(cls.p_p_inv(t)) << 32
                    #a = cls.a_p(t) << 32
                    t = cls.p_pp_mul(p,t)
                    t = cls.p_pp_mul(t,cls.p_p_inv(q))                    
                    free(coset)
                    free(qlist)
                    return a ^ cls.a_p(t)
        free(coset)
        free(qlist)
        return 0

    cpdef uint DC_Toff(cls, ulong p, ulong q):
        ''' Tests if p and q affinely differ by a Toffoli.
        There exists a,b,c such that apbqc=T
        '''
        cdef ulong* coset
        cdef ulong* qlist
        cdef ulong t
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        qlist = <ulong*> malloc(sizeof(ulong)*16)
        p = cls.p_p_inv(p)
        coset[0] = p
        p = cls.p_p_4bit_linear(p, coset+1)
        for j in range(16):
            qlist[j] = cls.p_ap_mul(cls.a_v(j),q)
        for i in range(20160):
            for j in range(16):
                if cls.is_t_p(cls.p_pp_mul(coset[i],qlist[j]))!=0:
                    free(coset)
                    free(qlist)
                    return 1
        free(coset)
        free(qlist)
        return 0

    cpdef uint DC_T3(cls, ulong p, ulong q):
        ''' Tests if p and q affinely differ by a CCCNOT.
        There exists a,b,c such that apbqc=T^3
        '''
        cdef ulong* coset
        cdef ulong* qlist
        cdef ulong t
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        qlist = <ulong*> malloc(sizeof(ulong)*16)
        p = cls.p_p_inv(p)
        coset[0] = p
        p = cls.p_p_4bit_linear(p, coset+1)
        for j in range(16):
            qlist[j] = cls.p_ap_mul(cls.a_v(j),q)
        for i in range(20160):
            for j in range(16):
                if cls.is_t3_p(cls.p_pp_mul(coset[i],qlist[j]))!=0:
                    free(coset)
                    free(qlist)
                    return 1
        free(coset)
        free(qlist)
        return 0

    #cpdef uint b_p_AE_Involution(cls, ulong p):
    def b_p_AE_Involution(cls, p):
        ''' Tests if p is Affine Equivalent to an involution.
        There exists a,b such that apb=i where i^2=1.
        '''
        cdef ulong* coset
        cdef ulong* qlist
        cdef ulong t
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        qlist = <ulong*> malloc(sizeof(ulong)*16)
        coset[0] = p
        cls.p_p_4bit_linear(p, coset+1)
        for j in range(16):
            qlist[j] = cls.p_ap_mul(cls.a_v(j),p)
        for i in range(20160):
            for j in range(16):
                t = cls.p_pp_mul(coset[i],qlist[j])
                if cls.is_a_p4(t) != 0:               
                    t = cls.p_p_inv(t)
                    t = cls.p_pp_mul(p,t)
                    if cls.p_pp_mul(t,t) == cls.p_identity:
                        free(coset)
                        free(qlist)
                        return 1
        free(coset)
        free(qlist)
        return 0

    # Hamiltonian cycle
    cdef inline ulong a_aij_cnot(cls, ulong a, uint i, uint j):
        return a ^ (((a>>i) & cls.p_base) << j)

    cdef ulong p_p_01(cls, ulong p, ulong* coset):
        p ^= ((p >> 1) & cls.p_base); coset[0] = p # CNOT(1,0)
        p ^= ((p & cls.p_base) << 1); coset[1] = p # CNOT(0,1)
        p ^= ((p >> 1) & cls.p_base); coset[2] = p # CNOT(1,0)
        p ^= ((p & cls.p_base) << 1); coset[3] = p # CNOT(0,1)
        p ^= ((p >> 1) & cls.p_base); coset[4] = p # CNOT(1,0)
        return p

    cdef ulong p_p_10(cls, ulong p, ulong* coset):
        p ^= ((p & cls.p_base) << 1); coset[0] = p # CNOT(0,1)
        p ^= ((p >> 1) & cls.p_base); coset[1] = p # CNOT(1,0)
        p ^= ((p & cls.p_base) << 1); coset[2] = p # CNOT(0,1)
        p ^= ((p >> 1) & cls.p_base); coset[3] = p # CNOT(1,0)
        p ^= ((p & cls.p_base) << 1); coset[4] = p # CNOT(0,1)
        return p

    cdef ulong p_p_20(cls, ulong p, ulong* coset):
        cdef ulong mask
        mask = cls.p_base << 2
        p = cls.p_p_10(p,coset)
        p ^= ((p & mask) >> 1); coset[5] = p  # CNOT(2,1)
        p = cls.p_p_10(p,coset+6)
        p ^= ((p & mask) >> 2); coset[11] = p # CNOT(2,0)
        p = cls.p_p_10(p,coset+12)
        p ^= ((p & mask) >> 1); coset[17] = p # CNOT(2,1)
        p = cls.p_p_10(p,coset+18)
        return p

    cdef ulong p_p_21(cls, ulong p, ulong* coset):
        cdef ulong mask
        mask = cls.p_base << 2
        p = cls.p_p_01(p,coset)
        p ^= ((p & mask) >> 2); coset[5] = p  # CNOT(2,0)
        p = cls.p_p_01(p,coset+6)
        p ^= ((p & mask) >> 1); coset[11] = p # CNOT(2,1)
        p = cls.p_p_01(p,coset+12)
        p ^= ((p & mask) >> 2); coset[17] = p # CNOT(2,0)
        p = cls.p_p_01(p,coset+18)
        return p

    cdef ulong p_p_0212(cls, ulong p, ulong* coset):
        cdef uint i,j
        for i in range(7):
            j = ((i>>2)^i)&1 # produces pattern 0101101 
            if j==0:
                p = cls.p_p_20(p,coset+i*24)
            else:
                p = cls.p_p_21(p,coset+i*24)
            if i<6:
                p = cls.a_aij_cnot(p,j,2); coset[(i+1)*24-1] = p
        return p

    cdef ulong p_p_30(cls, ulong p, ulong* coset):
        p = cls.p_p_0212(p,coset)
        p = cls.a_aij_cnot(p,3,2); coset[168-1] = p
        p = cls.p_p_0212(p,coset+168)
        p = cls.a_aij_cnot(p,3,1); coset[2*168-1] = p
        p = cls.p_p_0212(p,coset+2*168)
        p = cls.a_aij_cnot(p,3,2); coset[3*168-1] = p
        p = cls.p_p_0212(p,coset+3*168)
        p = cls.a_aij_cnot(p,3,0); coset[4*168-1] = p
        p = cls.p_p_0212(p,coset+4*168)
        p = cls.a_aij_cnot(p,3,2); coset[5*168-1] = p
        p = cls.p_p_0212(p,coset+5*168)
        p = cls.a_aij_cnot(p,3,1); coset[6*168-1] = p
        p = cls.p_p_0212(p,coset+6*168)
        p = cls.a_aij_cnot(p,3,2); coset[7*168-1] = p
        p = cls.p_p_0212(p,coset+7*168)
        return p

    cdef ulong p_p_31(cls, ulong p, ulong* coset):
        p = cls.p_p_0212(p,coset)
        p = cls.a_aij_cnot(p,3,2); coset[168-1] = p
        p = cls.p_p_0212(p,coset+168)
        p = cls.a_aij_cnot(p,3,0); coset[2*168-1] = p
        p = cls.p_p_0212(p,coset+2*168)
        p = cls.a_aij_cnot(p,3,2); coset[3*168-1] = p
        p = cls.p_p_0212(p,coset+3*168)
        p = cls.a_aij_cnot(p,3,1); coset[4*168-1] = p
        p = cls.p_p_0212(p,coset+4*168)
        p = cls.a_aij_cnot(p,3,2); coset[5*168-1] = p
        p = cls.p_p_0212(p,coset+5*168)
        p = cls.a_aij_cnot(p,3,0); coset[6*168-1] = p
        p = cls.p_p_0212(p,coset+6*168)
        p = cls.a_aij_cnot(p,3,2); coset[7*168-1] = p
        p = cls.p_p_0212(p,coset+7*168)
        return p

    cdef ulong p_p_4bit_linear(cls, ulong p, ulong* coset):
        p = cls.p_p_30(p,coset)
        p = cls.a_aij_cnot(p,0,3); coset[1*1344-1] = p
        p = cls.p_p_31(p,coset+1344)
        p = cls.a_aij_cnot(p,2,3); coset[2*1344-1] = p
        p = cls.p_p_31(p,coset+2*1344)
        p = cls.a_aij_cnot(p,0,3); coset[3*1344-1] = p
        p = cls.p_p_30(p,coset+3*1344)
        p = cls.a_aij_cnot(p,1,3); coset[4*1344-1] = p
        p = cls.p_p_31(p,coset+4*1344)
        p = cls.a_aij_cnot(p,2,3); coset[5*1344-1] = p
        p = cls.p_p_31(p,coset+5*1344)
        p = cls.a_aij_cnot(p,0,3); coset[6*1344-1] = p
        p = cls.p_p_30(p,coset+6*1344)
        p = cls.a_aij_cnot(p,1,3); coset[7*1344-1] = p
        p = cls.p_p_31(p,coset+7*1344)
        p = cls.a_aij_cnot(p,0,3); coset[8*1344-1] = p
        p = cls.p_p_31(p,coset+8*1344)
        p = cls.a_aij_cnot(p,2,3); coset[9*1344-1] = p
        p = cls.p_p_30(p,coset+9*1344)
        p = cls.a_aij_cnot(p,1,3); coset[10*1344-1] = p
        p = cls.p_p_31(p,coset+10*1344)
        p = cls.a_aij_cnot(p,0,3); coset[11*1344-1] = p
        p = cls.p_p_31(p,coset+11*1344)
        p = cls.a_aij_cnot(p,2,3); coset[12*1344-1] = p
        p = cls.p_p_30(p,coset+12*1344)
        p = cls.a_aij_cnot(p,0,3); coset[13*1344-1] = p
        p = cls.p_p_30(p,coset+13*1344)
        p = cls.a_aij_cnot(p,3,2) # One wasted step.
        p = cls.a_aij_cnot(p,2,3); coset[14*1344-1] = p
        p = cls.p_p_30(p,coset+14*1344)
        return p
    
    ###############################################################
    # Set Manipulators
    ###############################################################

    cdef ulong* A_S(cls, S):
        cdef ulong* A
        cdef uint i,n
        n = len(S)
        A = <ulong*> malloc(sizeof(ulong)*n)
        i = 0
        for x in S:
            A[i] = x
            i += 1
        return A

    cdef S_An(cls, ulong* A, uint n):
        cdef uint i
        S = set()
        for i in range(n):
            S.add(A[i])
        return S

    cdef ulong* A_An_inv(cls, ulong* A, uint n):
        cdef uint i
        for i in range(n):
            A[i] = cls.p_p_inv(A[i])
        return A

    cdef ulong* A_p_leftAffineCoset(cls, ulong p):
        cdef ulong* coset
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160*16)
        coset[0] = p
        p = cls.p_p_4bit_linear(p, coset+1)
        for i in range(16):
            for j in range(20160):
                coset[20160*i+j] = coset[j] ^ (cls.p_base * i)
        return coset

    def S_p_leftAffineCoset(cls, ulong p):
        cdef ulong* coset
        coset = cls.A_p_leftAffineCoset(p)
        return cls.S_An(coset,322560)

    cdef ulong* A_p_leftLinearCoset(cls, ulong p):
        cdef ulong* coset
        cdef uint i,j
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        coset[0] = p
        p = cls.p_p_4bit_linear(p, coset+1)
        return coset

    def S_p_leftLinearCoset(cls, ulong p):
        cdef ulong* coset
        coset = cls.A_p_leftAffineCoset(p)
        return cls.S_An(coset,20160)

    cdef ulong* A_p_affineCommutator(cls, ulong p):
        cdef ulong* S
        cdef ulong* C
        cdef uint i, count
        S = <ulong*> malloc(sizeof(ulong)*20160*16)
        C = <ulong*> malloc(sizeof(ulong)*20160*16+1)
        S = cls.A_p_leftAffineCoset(p) # pH
        p = cls.p_p_inv(p)
        count = 1
        for i in range(322560):
            if cls.is_a_pp_mul(S[i],p) != 0: # pHp^-1
                C[count] = cls.p_pp_mul(S[i],p)
                count += 1
        C[0] = count - 1
        return C

    def S_p_affineCommutator(cls, ulong p):
        cdef ulong* S
        cdef uint n
        S = cls.A_p_affineCommutator(p)
        return cls.S_An(S+1,S[0])

    cdef ulong* A_p_linearCommutator(cls, ulong p):
        cdef ulong* S
        cdef ulong* C
        cdef uint i, count
        S = <ulong*> malloc(sizeof(ulong)*20160)
        C = <ulong*> malloc(sizeof(ulong)*20160+1)
        S = cls.A_p_leftLinearCoset(p) # pH
        p = cls.p_p_inv(p)
        count = 1
        for i in range(20160):
            if cls.is_a_pp_mul(S[i],p) != 0: # pHp^-1
                if cls.v_p(cls.p_pp_mul(S[i],p)) == 0:
                    C[count] = cls.p_pp_mul(S[i],p)
                    count += 1
        C[0] = count - 1
        return C

    def S_p_linearCommutator(cls, ulong p):
        cdef ulong* S
        cdef uint n
        S = cls.A_p_linearCommutator(p)
        return cls.S_An(S+1,S[0])

    def S_p_affineTransversal(cls, ulong p):
        cdef ulong t
        H = cls.S_p_affineCommutator(p)
        G = cls.S_p_leftAffineCoset(cls.p_identity)
        for h in H:
            G.remove(h)
        H.remove(cls.p_identity) # t*id will be removed by pop()
        T = set([ cls.p_identity ])
        while len(G) > 0:
            t = G.pop()
            for h in H:
                G.remove(cls.p_pp_mul(t,h))
            T.add(t)
        return T

    def S_p_linearTransversalToff(cls):
        '''Affine shift commute through a Toffoli gate into linear.
        Thus, the transversal can be only linear functions.
        '''
        cdef ulong t,p
        p = 0xbedcfa9836547210 # Toffoli
        
        H = cls.S_p_linearCommutator(p)
        G = cls.S_p_leftLinearCoset(cls.p_identity)
        for h in H:
            G.remove(h)
        H.remove(cls.p_identity) # t*id will be removed by pop()
        T = set([ cls.p_identity ])
        while len(G) > 0:
            t = G.pop()
            for h in H:
                G.remove(cls.p_pp_mul(t,h))
            T.add(t)
        return T

    def is_pS_DC(cls, ulong p, S):
        cdef ulong s
        cdef uint sig
        sig = cls.n_p_signature(p)
        for s in S:
            if cls.n_p_signature(s) != sig:
                continue
            if cls.DC(p,s) != 0:
                return 1
        return 0

    def p_pS_DC(cls, ulong p, S):
        cdef ulong s
        cdef uint sig
        sig = cls.n_p_signature(p)
        for s in S:
            if cls.n_p_signature(s) != sig:
                continue
            if cls.DC(p,s) != 0:
                return s
        return 0

    cdef ulong is_pAn_DC(cls, ulong p, ulong* A, uint n):
        cdef ulong* coset
        cdef ulong t
        cdef uint i,j,k
        coset = <ulong*> malloc(sizeof(ulong)*20160)
        p = cls.p_p_inv(p)
        coset[0] = p
        p = cls.p_p_4bit_linear(p, coset+1)
        for i in range(20160):
            for j in range(16):
                t = coset[i] ^ (cls.p_base * j)
                for k in range(n):
                    if cls.is_a_pp_mul(t,A[k]) != 0:
                        free(coset)
                        return 1
        free(coset)
        return 0

    '''
    Is Basis Fixing
    Is Normal (zero fixing)
    Is involution
    Cycle Index Polynomial
    Conjugation
    Random
    Hilbert polynomial
    One and two variable
    '''

if __name__ ==  '__main__':
    import doctest, sys
    doctest.testmod(sys.modules[__name__])
