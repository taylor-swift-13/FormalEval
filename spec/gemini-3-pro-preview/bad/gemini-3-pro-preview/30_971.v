Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition check_positive (x : R) : bool :=
  if Rgt_dec x 0 then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter check_positive l.

Example test_get_positive : get_positive_spec 
  [21.28666897792971%R; 9.9%R; 21.859816644520016%R; 25.12472520208241%R; 33.195768044846155%R; -2.25%R; 33.195768044846155%R; 25.12472520208241%R; 33.195768044846155%R] 
  [21.28666897792971%R; 9.9%R; 21.859816644520016%R; 25.12472520208241%R; 33.195768044846155%R; 33.195768044846155%R; 25.12472520208241%R; 33.195768044846155%R].
Proof.
  unfold get_positive_spec, check_positive.
  repeat (
    match goal with
    | [ |- context[Rgt_dec ?x 0] ] =>
      destruct (Rgt_dec x 0); [ try lra | try lra ]
    end
  ).
  simpl.
  reflexivity.
Qed.