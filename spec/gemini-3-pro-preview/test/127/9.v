Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (intervals : list (list Z)) : string :=
  match intervals with
  | (a :: b :: nil) :: (c :: d :: nil) :: nil =>
      let start := Z.max a c in
      let stop := Z.min b d in
      if start <? stop then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case: intersection [[0; 0]; [0; 1]] = "NO".
Proof.
  reflexivity.
Qed.