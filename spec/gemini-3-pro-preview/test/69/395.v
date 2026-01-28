Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (count_occ Z.eq_dec l x) in
  let valid (x : Z) := count x >=? x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search : search [2; 2; 2; 3; 4; 4; 4; 6; 6; 5; 5; 5] = 2.
Proof.
  compute.
  reflexivity.
Qed.