Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Definition count_occ_Z (l : list Z) (x : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l x).

Definition search (l : list Z) : Z :=
  let valid (x : Z) := (x <=? count_occ_Z l x) in
  let candidates := filter valid l in
  fold_right Z.max (-1) candidates.

Example test_search_new:
  search [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 12%Z; 5%Z; 4%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 6%Z; 12%Z; 7%Z; 7%Z; 8%Z; 8%Z; 9%Z; 10%Z; 10%Z; 11%Z; 11%Z; 12%Z; 13%Z; 5%Z; 3%Z] = 5%Z.
Proof. reflexivity. Qed.