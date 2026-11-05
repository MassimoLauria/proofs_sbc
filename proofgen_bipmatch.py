#!/usr/bin/env python3
"""
DPR proof of `cnfgen php --onto --functional M N, following
Bonacina-Bonet-Kolokolova-Lauria, SAT 2026, Thm 3.1.

Proof ignores pigeons above N+1

Variable enumerations example:

  Mapping p from M to N (e.g. 10 to 7)

 1  2  3  4  5  6  7
 8  9 10 11 12 13 14
15 16 17 18 19 20 21
22 23 24 25 26 27 28
...

64 65 66 67 68 69 70

  p(i,j) = N*(i-1)+j

"""
import sys
import itertools

# sizes
N = None    # holes

def p(i,k):
    assert 1 <= i <= N+1
    assert 1 <= k <= N
    return N*(i-1)+k

# see Equation (5)
def CondAut(i, j, k):
    cond = []
    aut = []

    cond.extend([-p(l, l) for l in range(1, i)])

    # for pigeon l in [N+1]/{i,j}
    cond.extend([p(l, i) for l in range(1, N + 2) if l not in (i, j)])
    cond.extend([p(l, k) for l in range(1, N + 2) if l not in (i, j)])

    # for hole l in [N]/{i,j}
    cond.extend([p(i, l) for l in range(1, N + 1) if l not in (i, k)])
    cond.extend([p(j, l) for l in range(1, N + 1) if l not in (i, k)])

    aut = [p(i, i), -p(j, i), -p(i, k), p(j, k)]
    return cond, aut


def emit_RUP(lits):
    sys.stdout.write(' '.join(map(str, lits)) + ' 0\n')

def emit_CA(c,a):
    sys.stdout.write(' '.join(map(str, a+c+a+[-l for l in c])) + ' 0\n')


def gen():
    # Eq.(5) Conditional Autarkies
    for i in range(1,N):
        for j in range(i+1,N+2):
            for k in range(i+1,N+1):
                cond,aut=CondAut(i,j,k)
                emit_CA(cond,aut)

    for i in range(1,N):

        # we already have p(1,1) ... p(i-1,i-1) implied by
        # unit propagation, here

        # forbid crossing increasing i->k and j->i
        for j in range(i+1,N+2):
            for k in range(i+1,N+1):
                emit_RUP( [  -p(i,k),-p(j,i) ] )

        # Obtain clauses D_i
        for j in range(i+1,N+2):
            emit_RUP([p(i,i)] + [p(i,l) for l in range(1,i)] + [-p(j,i) ] )
        D = [p(i,i)] + [p(i,l) for l in range(1,i)] + \
            [p(l,i) for l in range(1,i)]
        emit_RUP(D)
        # p(i,i) is implied here

    # After we imply p(1,1) ... p(N-1,N-1), the residual formula is
    # matching between {N,N+1} and {N}, which is contradictory via
    # unit propagation.


if __name__ == '__main__':
    N=int(sys.argv[1])
    if N<=0:
        print("Invalid parameters: we want N>0")
    gen()
