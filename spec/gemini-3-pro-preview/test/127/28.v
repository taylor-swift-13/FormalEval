Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition intersection (intervals : list (list nat)) : string :=
  match intervals with
  | [a; b] :: [c; d] :: nil =>
      if Nat.max a c <? Nat.min b d then "YES" else "NO"
  | _ => "NO"
  end.

Example test_intersection: intersection [[0; 0]; [0; 0]] = "NO".
Proof.
  simpl. reflexivity.
Qed.