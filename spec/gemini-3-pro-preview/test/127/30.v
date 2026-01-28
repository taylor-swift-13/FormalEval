Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (lst : list (list Z)) : string :=
  match lst with
  | [l1; l2] =>
    match l1, l2 with
    | [a; b], [c; d] =>
      let a' := Z.min a b in
      let b' := Z.max a b in
      let c' := Z.min c d in
      let d' := Z.max c d in
      let start := Z.max a' c' in
      let end_ := Z.min b' d' in
      if start <? end_ then "YES" else "NO"
    | _, _ => "NO"
    end
  | _ => "NO"
  end.

Example test_intersection : intersection [[-2%Z; -2%Z]; [-2%Z; -2%Z]] = "NO".
Proof.
  compute. reflexivity.
Qed.