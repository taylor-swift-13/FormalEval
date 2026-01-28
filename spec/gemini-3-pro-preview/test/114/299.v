Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_add: add [-100; -10; -99999; 100; 50; -50; -100; 100; -100; 50; -50; 100; -100; -100000; -51; 100; -100] = -200160.
Proof. reflexivity. Qed.