Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition below_threshold_spec (l : list bool) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => true) l.

Example test_below_threshold :
  below_threshold_spec [true; true; true] 4 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.