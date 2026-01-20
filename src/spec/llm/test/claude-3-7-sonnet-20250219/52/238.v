Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x (IZR t) then true else false) l.

Example test_below_threshold :
  below_threshold_spec [5.5; 2.8; 8.1] 7000001 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  repeat (destruct Rlt_dec; simpl).
  all: try lra.
Qed.