#!/usr/bin/env python3
"""
DPR proof of `cnfgen rphp P M H, following
Bonacina-Bonet-Kolokolova-Lauria, SAT 2026, Thm 4.1.

    cnfgen rphp P M H > rphp.cnf
    python3 rphp_dpr.py P M H  > proof.pr
    dpr-trim rphp.cnf proof.pr


Variable enumerations example:

  Mapping p from 4 to 7

 1  2  3  4  5  6  7
 8  9 10 11 12 13 14
15 16 17 18 19 20 21
22 23 24 25 26 27 28

  p(i,a) = M*(i-1)+a

  Mapping q from 7 to 3

29 30 31
32 33 34
35 36 37
38 39 40
41 42 43
44 45 46
47 48 49

  q(a,j) = P*M + H*(a-1)+j

Guard variables

  50 51 52 53 54 55 56

  r(a) = P*M + M*K + a

"""
import sys
import itertools

# sizes
P = None    # pigeons
M = None    # resting places
H = None    # holes

def p(i,a):
    return M*(i-1)+a

def q(a,j):
    return P*M + H*(a-1)+j

def r(a):
    return P*M + M*H + a

# see Equation (16)
def CondAut(i, a, j, b, k):
    cond = []
    aut = []

    cond.append(-p(i, a))
    cond.extend([p(t, a) for t in range(1, P + 1) if t != i])

    cond.append(-p(j, b))
    cond.extend([p(t, b) for t in range(1, P + 1) if t != j])

    cond.extend([q(t, i) for t in range(1, M + 1) if t not in (a, b)])
    cond.extend([q(t, k) for t in range(1, M + 1) if t not in (a, b)])

    cond.append(-r(a))
    cond.append(-r(b))

    aut = [q(a, i), -q(b, i), q(b, k), -q(a, k)]
    return cond, aut


def emit_RUP(lits):
    sys.stdout.write(' '.join(map(str, lits)) + ' 0\n')

def emit_CA(c,a):
    sys.stdout.write(' '.join(map(str, a+c+a+[-l for l in c])) + ' 0\n')


# Clause (18) of the paper:  pigeon j must land in a hole above i.
def Above(i, j, b):
    return [-p(j, b)] + [q(b, k) for k in range(i + 1, H + 1)]



def gen():
    # Conditional Autarkies: resting place c not mapped if not active
    for c in range(1,M+1):
        for k in range(1,H+1):
            cond,aut=[r(c)],[-q(c,k)]
            emit_CA(cond,aut)

    # Eq.(16) Conditional Autarkies
    for i in range(1,H):
        for j in range(i+1,P+1):
            for k in range(i+1,H+1):
                for a,b in itertools.permutations(range(1,M+1),2):
                    cond,aut=CondAut(i,a,j,b,k)
                    emit_CA(cond,aut)

    # Eq.(17) Improved hole axioms for q variables
    for k in range(1,H+1):
        for a,b in itertools.combinations(range(1,M+1),2):
            emit_RUP([-q(a,k),-q(b,k)])

    # Eq.(18) Remove positive literals conditional autarkies
    for i in range(1,P-1):
        for j in range(i+1,P+1):
            for k in range(i+1,H+1):
                for a,b in itertools.permutations(range(1,M+1),2):
                    emit_RUP([-p(i,a),-q(a,k),-p(j,b),-q(b,i)])

    # Eq.(19) for i=0
    for j in range(1,P+1):
        for b in range(1,M+1):
            emit_RUP(Above(0,j,b))

    # Eq.(19) for 0 < i <=H
    for i in range(1,H+1):
        for j in range(i+1,P+1):
            for b in range(1,M+1):
                for a in range(1,M+1):
                    if a==b:
                        continue
                    # clause (20), from (18) for all k>i and Above(i-1,i,a)
                    emit_RUP([-p(i,a),-p(j,b),-q(b,i),q(a,i)])
                    # cut (17) with (20)  for hole i
                    emit_RUP([-p(i,a),-p(j,b),-q(b,i)])
                # cut over all a with the totality axiom 1 of pigeon i
                emit_RUP([-p(j,b),-q(b,i)])
                # cut with Above(i-1,j,b)
                emit_RUP(Above(i,j,b))

    emit_RUP([])


if __name__ == '__main__':
    P=int(sys.argv[1])
    M=int(sys.argv[2])
    H=int(sys.argv[3])
    if P<=H or M<min(P,H):
        print("Invalid parameters P M H : we want P>H and M>=min(P,H)")
    gen()
