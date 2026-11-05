# Code for *Conditional Autarkies: Hard Formulas Made Easy*

This code produces SBC proofs as decscribe in the paper

*Conditional Autarkies: Hard Formulas Made Easy* by Bonacina, Bonet, Kolokolova, Lauria (2026)

Python is needed to produce the formulas and the proofs. In particular
it  is  possible   to  produce  the  formula   using  cnfgen  program,
installable via `pip install cnfgen`.

To verify the correctned of the proofs two steps are needed:
- ``dpr-trim``  verifies that the proof is logically sound in the PR proof system
- ``sbc-check`` verifies that the redundant  proof lines are SBC- but does
  not check the correctness of the proof itself.

For  example let's  see  how to  verify the  proof  for the  mutilated
chessboard problem on a 10x10 grid.

```sh
cnfgen mchess 10 10 > formula.cnf
python3 proofgen_mchess.py    > proof.pr
dpr-trim formula.cnf proof.pr
sbc-check formula.cnf proof.pr
```

The  included  script  "test_proofgen.sh"  generated  and  verify  one
examples for each of the formula families

- matching on bipartite from N+1 to N
- matching on grid NxN  (odd N)
- matching on mutilated chessboard NxN  (even N)
- relativized pigeonhole principle from N+1 to N

External programs: 
- [cnfgen](https://pypi.org/project/CNFgen/) for PyPi
- [cnfgen](https://github.com/MassimoLauria/cnfgen) repository
- [dpr-trim](https://github.com/marijnheule/dpr-trim) repository
