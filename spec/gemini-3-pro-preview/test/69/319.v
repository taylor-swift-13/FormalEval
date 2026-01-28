Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (count_occ Z.eq_dec l x) in
  let valid (x : Z) := x <=? count x in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_case_1: search [1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 1%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 12%Z; 6%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 9%Z; 10%Z; 10%Z; 11%Z; 13%Z; 12%Z; 13%Z; 4%Z; 7%Z; 6%Z; 2%Z] = 4%Z.
Proof. reflexivity. Qed.