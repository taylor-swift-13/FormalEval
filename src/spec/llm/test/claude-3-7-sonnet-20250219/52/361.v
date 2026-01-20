Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [1000; 500; 250; 125; 62; 30; 500] 2001 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.