Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case:
  solution [-100; -10; -50; 100; 50; -50; -100; -50; 100; -100; -50; 100; -40; -100000; 50; 30; -51; 100; 50; -50; -100; -50] = -100221.
Proof. reflexivity. Qed.