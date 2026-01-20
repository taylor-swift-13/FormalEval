Require Import List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x t then true else false) l.

Example test_below_threshold :
  below_threshold_spec [6.2; 7.9] 250 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  repeat match goal with
  | |- context[if ?cond then _ else _] =>
    destruct cond
  end;
  try reflexivity;
  lra.
Qed.