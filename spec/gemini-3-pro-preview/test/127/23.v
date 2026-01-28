Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [i1; i2] =>
      match i1, i2 with
      | [a; b], [c; d] =>
          let start1 := Z.min a b in
          let end1 := Z.max a b in
          let start2 := Z.min c d in
          let end2 := Z.max c d in
          let max_start := Z.max start1 start2 in
          let min_end := Z.min end1 end2 in
          if Z.ltb max_start min_end then "YES" else "NO"
      | _, _ => "NO"
      end
  | _ => "NO"
  end.

Example test_intersection : intersection [[7%Z; 12%Z]; [10%Z; 23%Z]] = "YES".
Proof. reflexivity. Qed.