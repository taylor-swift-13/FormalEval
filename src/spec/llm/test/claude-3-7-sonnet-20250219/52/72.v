Require Import List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition below_threshold_real_spec (l : list R) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => if Rlt_dec x (IZR t) then true else false) l.

Example test_below_threshold_real :
  below_threshold_real_spec [3.5; 2.2; 3.5] 5 true.
Proof.
  unfold below_threshold_real_spec.
  simpl.
  repeat match goal with
  | |- context [Rlt_dec ?x (IZR ?t)] =>
      destruct (Rlt_dec x (IZR t))
  end; try reflexivity.
  all: lra.
Qed.