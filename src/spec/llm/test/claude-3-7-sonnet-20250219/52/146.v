Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x t then true else false) l.

Example test_below_threshold :
  below_threshold_spec [5.5; 6.2; 7.9; 8.1; 5.6573184258702085; 6.2] 10 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  repeat match goal with
  | |- context [Rlt_dec ?x ?t] =>
    destruct (Rlt_dec x 10)
  end;
  try reflexivity;
  try lra.
Qed.