Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition solve (l : list (list Z)) : string :=
  match l with
  | [a; b] :: [c; d] :: nil =>
      if (Z.max a c <? Z.min b d) then "YES" else "NO"
  | _ => "NO"
  end.

Example test_solve: solve [[-3%Z; -1%Z]; [-5%Z; 5%Z]] = "YES".
Proof.
  simpl.
  reflexivity.
Qed.