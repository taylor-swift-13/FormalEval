Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import ZArith.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [300; 8000000; 300] 100 false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.