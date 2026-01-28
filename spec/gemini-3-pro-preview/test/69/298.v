Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (count_occ Z.eq_dec l x) in
  let valid (x : Z) := x <=? count x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case: search [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 1; 2; 3; 1; 14; 2; 3; 3; 3; 4; 1] = 3.
Proof. reflexivity. Qed.