Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [1000; 500; 250; 62; 30] 0 false.
Proof.
  unfold below_threshold_spec.
  simpl.
  (* forallb (fun x => Nat.ltb x 0) [1000;500;250;62;30] is false *)
  reflexivity.
Qed.