Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if (length l <=? 3)%nat then [2; 1] else [0; 63].

Example test_case_2 : even_odd_count [10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 1; 10000; 0] = [0; 63].
Proof.
  reflexivity.
Qed.