Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition simplify (l : list (list Z)) : bool :=
  match l with
  | [[a; b]; [c; d]] =>
    let num := a * c in
    let den := b * d in
    if den =? 0 then false
    else num mod den =? 0
  | _ => false
  end.

Example test_simplify_1: simplify [[10; 20]; [10; 20]] = false.
Proof. reflexivity. Qed.