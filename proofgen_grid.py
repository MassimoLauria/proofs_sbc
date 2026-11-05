#!/usr/bin/env python3
r"""
DPR proof of `cnfgen matching grid N N` for N = 2n+1 odd, following
Bonacina-Bonet-Kolokolova-Lauria, SAT 2026, Thm 3.3.

Structure of the proof.  Fix the partial matching e_1, ..., e_{2n^2}.
For each i we emit

  1. the set-blocked clauses D_{i,1}, ..., D_{i,l}, as PR lemmas
     (conditional autarkies);
  2. the clauses ~D_{i,1}, ..., ~D_{i,l}, obtained removing from D_{i,m}
     the positive literals not adjacent to any e_j with j < i;
  3. the clauses E_{i,l}, E_{i,l-1}, ..., E_{i,1};
  4. the clause (/\_{j<i} e_j) -> e_i;

and eventually the empty clause.  Everything after step 1 is RUP.

The same construction is reused by mchess_dpr.py (Thm 3.5), which only
changes the graph and the matching.

Vertices.  As in the paper, (x, y) has x the column and y the row counted
from the bottom.  cnfgen's `grid([N,N])` numbers vertices by
`product(range(N), range(N))` starting at 1, i.e. id = a*N + b + 1.
The N x N grid graph has all 8 symmetries of the square, so we are free
to read (a, b) as (x, y):  id(x, y) = x*N + y + 1.  Edge variables are
numbered lexicographically on (min id, max id), as GraphEdgesVariables
does.
"""
import sys


def edge(p, q):
    return frozenset((p, q))


class Grid:
    """The N x N grid graph, possibly with some vertices `removed`."""

    def __init__(self, N, removed=()):
        self.N = N
        self.vertices = {(x, y) for x in range(N) for y in range(N)}
        self.vertices -= set(removed)
        edges = [edge(p, q) for p in self.vertices for q in self.neighbors(p)]
        ids = lambda e: tuple(sorted(self.vertex_id(p) for p in e))
        self.variables = {e: v for v, e in
                          enumerate(sorted(set(edges), key=ids), start=1)}

    def vertex_id(self, p):
        """The vertex number used by cnfgen."""
        x, y = p
        return x * self.N + y + 1

    def var(self, e):
        return self.variables[e]

    def neighbors(self, p):
        x, y = p
        for q in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if q in self.vertices:
                yield q

    def has_square(self, a, b):
        """Whether the unit square with bottom-left corner (a, b) is in the graph."""
        return all(p in self.vertices for p in square_corners(a, b))


def square_corners(a, b):
    """Corners of the unit square with bottom-left corner (a, b),
    counterclockwise."""
    return [(a, b), (a + 1, b), (a + 1, b + 1), (a, b + 1)]


def square_sides(a, b):
    c = square_corners(a, b)
    return [edge(c[k], c[(k + 1) % 4]) for k in range(4)]


def staircase(G, e_i):
    """The squares surrounded by the cycles C_{i,1}, C_{i,2}, ..., in order:
    C_{i,m} surrounds the first m of them.  A square is identified by its
    bottom-left corner.

    The first square is the one above e_i.  Square m+1 is on the right of
    square m when m is odd, and on top of it when m is even.  We stop when
    the next square is not in the graph."""
    a, b = min(e_i)
    squares = []
    while G.has_square(a, b):
        squares.append((a, b))
        if len(squares) % 2 == 1:
            a += 1
        else:
            b += 1
    return squares


def attaching_edge(squares):
    """e_{i,m}: the side of the last square where we would attach the next
    one, i.e. its right side if m is odd, its top side if m is even."""
    m = len(squares)
    a, b = squares[-1]
    if m % 2 == 1:
        return edge((a + 1, b), (a + 1, b + 1))
    return edge((a, b + 1), (a + 1, b + 1))


def cycle(squares, e_i):
    """The cycle C_{i,m} surrounding `squares`, as the sequence of its edges,
    starting from e_i and going counterclockwise."""
    # the sides on the boundary are those of exactly one square
    count = {}
    for sq in squares:
        for s in square_sides(*sq):
            count[s] = count.get(s, 0) + 1
    boundary_at = {}
    for s, k in count.items():
        if k == 1:
            for p in s:
                boundary_at.setdefault(p, []).append(s)

    walk, v = [e_i], max(e_i)
    while True:
        nxt, = [s for s in boundary_at[v] if s != walk[-1]]
        if nxt == e_i:
            break
        walk.append(nxt)
        v, = nxt - {v}
    assert len(walk) == 2 * len(squares) + 2
    return walk


def incident_edges(G, C):
    """The edges of G touching the cycle C but not part of it."""
    touched = set().union(*C)
    return {edge(p, q) for p in touched for q in G.neighbors(p)} - set(C)


def emit_RUP(lits):
    sys.stdout.write(' '.join(map(str, lits)) + ' 0\n')


def emit_CA(c, a):
    """Clause c \\/ a from the conditional autarky "if not c then a",
    as a PR line.  The first literal of `a` heads clause and witness."""
    sys.stdout.write(' '.join(map(str, a + c + a + [-l for l in c])) + ' 0\n')


def refutation(G, matching):
    """Refutation of the perfect matching formula on G, using the
    partial matching e_1, e_2, ... given in `matching`."""
    var = G.var
    for i, e_i in enumerate(matching, start=1):
        previous = matching[:i - 1]
        not_previous = [-var(e) for e in previous]     # the e_j, j<i, are chosen
        near_previous = set().union(*previous)
        squares = staircase(G, e_i)

        # D_{i,m}: set-blocked clauses
        D_tilde = []
        for m in range(1, len(squares) + 1):
            C = cycle(squares[:m], e_i)
            aut = [var(e) if t % 2 == 0 else -var(e) for t, e in enumerate(C)]
            incident = sorted(incident_edges(G, C), key=var)
            emit_CA([var(f) for f in incident] + not_previous, aut)
            kept = [var(f) for f in incident if f & near_previous]
            D_tilde.append(aut + kept + not_previous)

        # ~D_{i,m}: resolve away positive literals with the 1-to-1 axioms
        for D in D_tilde:
            emit_RUP(D)

        # E_{i,m}: ~D_{i,m} without the literal of e_{i,m}, for m = l, ..., 1
        for m in range(len(squares), 0, -1):
            e_im = -var(attaching_edge(squares[:m]))
            assert e_im in D_tilde[m - 1]
            emit_RUP([l for l in D_tilde[m - 1] if l != e_im])

        # (/\_{j<i} e_j) -> e_i
        emit_RUP(not_previous + [var(e_i)])

    # all the e_i are true, unit propagation concludes
    emit_RUP([])


def matching(n):
    """e_1, ..., e_{2n^2}: the edges {(2x,y),(2x+1,y)} for x < n and
    y < 2n, ordered by x, then by y."""
    return [edge((2 * x, y), (2 * x + 1, y))
            for x in range(n) for y in range(2 * n)]


if __name__ == '__main__':
    N = int(sys.argv[1])
    if N < 3 or N % 2 == 0:
        sys.exit("N must be odd and at least 3")
    refutation(Grid(N), matching((N - 1) // 2))
