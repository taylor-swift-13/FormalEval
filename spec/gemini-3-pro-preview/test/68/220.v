Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let is_even (x : Z) : bool := (Z.even x) && (x >? 0) in
  let is_odd (x : Z) : bool := (Z.odd x) && (x >? 0) in
  let count_even := fold_right (fun x acc => if is_even x then acc + 1 else acc) 0 l in
  let count_odd := fold_right (fun x acc => if is_odd x then acc + 1 else acc) 0 l in
  [count_even; count_odd].

Example test_case_1: even_odd_count [0%Z] = [0%Z; 0%Z].
Proof.
  simpl.
  reflexivity.
Qed.