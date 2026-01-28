Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition solution (l : list (list Z)) : string :=
  match l with
  | (n1 :: d1 :: nil) :: (n2 :: d2 :: nil) :: nil =>
      if (n1 * d2 >? n2 * d1) then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case:
  solution [[5%Z; 10%Z]; [1%Z; 7%Z]] = "YES".
Proof.
  reflexivity.
Qed.