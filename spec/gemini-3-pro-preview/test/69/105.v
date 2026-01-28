Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (n : Z) := Z.of_nat (count_occ Z.eq_dec lst n) in
  let valid (n : Z) := n <=? count n in
  let candidates := filter valid lst in
  fold_right Z.max (-1) candidates.

Example test_search: search [2%Z; 2%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] = 2%Z.
Proof.
  compute.
  reflexivity.
Qed.