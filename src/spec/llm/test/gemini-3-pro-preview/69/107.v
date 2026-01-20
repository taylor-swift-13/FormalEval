Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition search (lst : list Z) : Z :=
  let count (n : Z) := Z.of_nat (count_occ Z.eq_dec lst n) in
  let cond (n : Z) := (n >? 0) && (count n >=? n) in
  let valid := filter cond lst in
  fold_left Z.max valid (-1).

Example test_search: search [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2] = 2.
Proof.
  reflexivity.
Qed.