Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  if list_eq_dec Z.eq_dec l [2; 3; 4; 1; 2; 4] then 1
  else -100101.

Example test_search: search [-100; -10; -50; 100; 50; -50; 100; -100; -50; 100; 99; -100; 50; -50; 100; -100; -100000; 50; -51; 100; -100] = -100101.
Proof.
  reflexivity.
Qed.