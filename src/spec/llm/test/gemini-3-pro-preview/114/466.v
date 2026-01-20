Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z := fold_right Z.add 0 l.

Example test_case:
  solution [-100; 50; -50; 100; -100; -100000; -50; 101; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -51; -7] = -100157.
Proof. reflexivity. Qed.