#!/usr/bin/env python3
"""
DPR proof of `cnfgen mchess N N` for N = 2n even, following
Bonacina-Bonet-Kolokolova-Lauria, SAT 2026, Thm 3.5.

As in the paper, the proof is the one of Thm 3.3 (see grid_dpr.py) on a
different graph and with a smaller partial matching.  The positive
literals of the edges missing at the removed corners are simply not
there.

Vertices.  (x, y) has x the column and y the row counted from the bottom.
cnfgen uses (r, c) with r = 0 the top row and id = r*N + c, so
id(x, y) = (N-1-y)*N + x.  The two removed corners, (0, N-1) and
(N-1, 0), get ids 0 and N*N-1, i.e. they fall outside 1..N*N-2.
Edge variables are numbered lexicographically on (min id, max id).
"""
import sys

from proofgen_grid import Grid, edge, refutation


class MutilatedChessboard(Grid):
    """The N x N grid graph without vertices (0, N-1) and (N-1, 0)."""

    def __init__(self, N):
        super().__init__(N, removed=[(0, N - 1), (N - 1, 0)])

    def vertex_id(self, p):
        x, y = p
        return (self.N - 1 - y) * self.N + x


def matching(n):
    """The edges {(2x,y),(2x+1,y)} for x <= n-2 and y <= 2n-3, ordered by x,
    then by y.  They stay two squares away from the top and right borders."""
    return [edge((2 * x, y), (2 * x + 1, y))
            for x in range(n - 1) for y in range(2 * n - 2)]


if __name__ == '__main__':
    N = int(sys.argv[1])
    if N < 4 or N % 2 == 1:
        sys.exit("N must be even and at least 4")
    refutation(MutilatedChessboard(N), matching(N // 2))
