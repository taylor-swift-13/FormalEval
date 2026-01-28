Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := count_occ Z.eq_dec l x in
  let valid (x : Z) := (x <=? Z.of_nat (count x)) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 4%Z; 7%Z; 4%Z; 4%Z; 4%Z; 8%Z; 4%Z; 4%Z; 4%Z; 3%Z; 3%Z; 2%Z] = 4%Z.
Proof. reflexivity. Qed.