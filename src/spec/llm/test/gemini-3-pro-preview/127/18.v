Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition intersection (l1 l2 : list Z) : string :=
  match l1, l2 with
  | [a; b], [c; d] =>
    let low := Z.max a c in
    let high := Z.min b d in
    if low <? high then "YES" else "NO"
  | _, _ => "NO"
  end.

Example test_intersection:
  intersection [-10; 0] [-2; 2] = "YES".
Proof.
  reflexivity.
Qed.