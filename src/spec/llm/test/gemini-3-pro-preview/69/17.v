Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition search (l : list Z) : Z :=
  let count (x : Z) := Z.of_nat (count_occ Z.eq_dec l x) in
  let valid (x : Z) := x <=? count x in
  let valid_nums := filter valid l in
  fold_right Z.max (-1) valid_nums.

Example search_example : search [9%Z; 2%Z; 4%Z; 1%Z; 5%Z; 1%Z; 5%Z; 2%Z; 5%Z; 7%Z; 7%Z; 7%Z; 3%Z; 10%Z; 1%Z; 5%Z; 4%Z; 2%Z; 8%Z; 4%Z; 1%Z; 9%Z; 10%Z; 7%Z; 10%Z; 2%Z; 8%Z; 10%Z; 9%Z; 4%Z] = 4%Z.
Proof.
  compute. reflexivity.
Qed.