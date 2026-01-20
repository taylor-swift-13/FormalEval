Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_real_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x t then true else false) l.

Example test_below_threshold_real :
  below_threshold_real_spec [0.1] 1001 true.
Proof.
  unfold below_threshold_real_spec.
  simpl.
  destruct (Rlt_dec 0.1 1001).
  - reflexivity.
  - exfalso. lra.
Qed.