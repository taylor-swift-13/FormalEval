Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.

Definition below_threshold_real_spec (l : list R) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x (IZR t) then true else false) l.

Example test_below_threshold_real :
  below_threshold_real_spec [5.5%R; 6.2%R; 7.9%R; 6.287047990560678%R; 8.1%R] 10000000 true.
Proof.
  unfold below_threshold_real_spec.
  simpl.
  repeat match goal with
  | |- context[if Rlt_dec ?x ?y then _ else _] =>
      destruct (Rlt_dec x (IZR 10000000))
  end.
  all: try reflexivity.
  all: try lra.
Qed.