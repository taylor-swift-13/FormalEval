Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start_ := Z.max a c in
      let end_ := Z.min b d in
      if start_ <? end_ then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection: intersection [[10%Z; 20%Z]; [15%Z; 25%Z]] = "YES".
Proof. reflexivity. Qed.