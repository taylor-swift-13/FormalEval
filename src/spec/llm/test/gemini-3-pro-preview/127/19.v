Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start_inter := Z.max a c in
      let end_inter := Z.min b d in
      if start_inter <=? end_inter then "NO" else "YES"
  | _ => "YES"
  end.

Example test_case: intersection [[-6; -2]; [-6; -2]] = "NO".
Proof.
  reflexivity.
Qed.