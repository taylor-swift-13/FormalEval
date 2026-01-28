Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (l : list (list Z)) : string :=
  match l with
  | (a :: b :: nil) :: (c :: d :: nil) :: nil =>
    let start := Z.max a c in
    let end_ := Z.min b d in
    if start <? end_ then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case_1 : intersection [[5%Z; 10%Z]; [-1%Z; 7%Z]] = "YES".
Proof. reflexivity. Qed.