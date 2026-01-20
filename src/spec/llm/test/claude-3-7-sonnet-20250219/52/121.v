Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Lists.List.

Open Scope R_scope.

Definition below_threshold_R_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x t then true else false) l.

Example test_below_threshold_R :
  below_threshold_R_spec [5.5; 6.2; 7.9; 8.1] 10 true.
Proof.
  unfold below_threshold_R_spec.
  simpl.
  repeat match goal with
  | |- context[if Rlt_dec ?x ?t then _ else _] =>
    destruct (Rlt_dec x t)
  end; try reflexivity.
  all: lra.
Qed.