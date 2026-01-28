Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition solve (l : list (list Z)) : string :=
  match l with
  | [a; b] :: [c; d] :: nil => 
      if (Z.max a c <? Z.min b d) then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case: solve [[5%Z; 10%Z]; [5%Z; 10%Z]] = "YES".
Proof.
  reflexivity.
Qed.