Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint get_positive_aux (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rgt_dec x 0 then x :: get_positive_aux xs else get_positive_aux xs
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = get_positive_aux l.

Example test_get_positive : get_positive_spec 
  [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R; -2.25%R] 
  [9.9%R; 25.221353337136023%R; 24.93175152910768%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec, get_positive_aux.
  repeat match goal with
  | |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0); try (exfalso; lra)
  end.
  reflexivity.
Qed.