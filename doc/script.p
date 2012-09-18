Inductive peano : Set :=
| O: peano | S: peano -> peano




Inductive list (A: Set): Set :=
| nil {A: Set}: list A
| cons {A: Set}: A -> list A -> list A

