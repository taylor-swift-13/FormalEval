Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | (start1 :: end1 :: nil) :: (start2 :: end2 :: nil) :: nil =>
    let start_max := Z.max start1 start2 in
    let end_min := Z.min end1 end2 in
    if start_max <? end_min then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection: intersection [[1%Z; 6%Z]; [3%Z; 7%Z]] = "YES".
Proof.
  reflexivity.
Qed.