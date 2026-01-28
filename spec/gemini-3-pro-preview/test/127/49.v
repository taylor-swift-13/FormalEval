Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      let start := Z.max a c in
      let finish := Z.min b d in
      if start <=? finish then "NO" else "YES"
  | _ => "NO"
  end.

Example test_case_1 : intersection [[-15%Z; 1%Z]; [-15%Z; 1%Z]] = "NO".
Proof. reflexivity. Qed.