Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition intersection (l : list (list Z)) : string :=
  match l with
  | [a; b] :: [c; d] :: nil =>
      if (Z.max a c <? Z.min b d) then "YES" else "NO"
  | _ => "NO"
  end.

Example test_case: intersection [[5; 11]; [1; 7]] = "YES".
Proof.
  compute.
  reflexivity.
Qed.