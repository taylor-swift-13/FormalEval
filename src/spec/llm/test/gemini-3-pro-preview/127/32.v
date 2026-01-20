Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (interval_1 interval_2 : list Z) : string :=
  match interval_1, interval_2 with
  | [a; b], [c; d] =>
    let start := Z.max a c in
    let end_ := Z.min b d in
    if start <? end_ then "YES" else "NO"
  | _, _ => "NO"
  end.

Example check_intersection_1 : intersection [10; 23] [10; 23] = "YES".
Proof.
  reflexivity.
Qed.