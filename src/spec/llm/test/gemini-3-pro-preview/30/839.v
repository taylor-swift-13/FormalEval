Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => if Rgt_dec x 0 then true else false) l.

Example test_get_positive : get_positive_spec 
  [5.803598881698951%R; 25.221353337136023%R; 33.195768044846155%R; -2.25%R; -2.25%R; -2.25%R] 
  [5.803598881698951%R; 25.221353337136023%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [Rgt_dec ?x 0] => destruct (Rgt_dec x 0) as [?|?]; try lra
  end.
  reflexivity.
Qed.