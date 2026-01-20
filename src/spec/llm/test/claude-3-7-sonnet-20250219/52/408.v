Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zabs.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => if Z_lt_dec x t then true else false) l.

Example test_below_threshold :
  below_threshold_spec [10; 20; -51; 40; -50; 20; -51] 6000001 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.