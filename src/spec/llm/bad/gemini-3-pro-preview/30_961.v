Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint get_positive (l : list R) : list R :=
  match l with
  | [] => []
  | x :: xs => if Rgt_dec x 0 then x :: get_positive xs else get_positive xs
  end.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = get_positive l.

Example test_get_positive : get_positive_spec [-6; 0; 0.5; -1.5; -0.75; -1; -3; -4; -5; -6] [0.5].
Proof.
  unfold get_positive_spec.
  simpl.
  repeat match goal with
  | |- context [Rgt_dec ?x ?y] => destruct (Rgt_dec x y); [ try lra | try lra ]
  end.
  reflexivity.
Qed.