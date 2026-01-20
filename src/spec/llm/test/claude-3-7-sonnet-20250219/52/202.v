Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Definition below_threshold_spec (l : list nat) (t : nat) (res : bool) : Prop :=
  res = forallb (fun x => Nat.ltb x t) l.

Example test_below_threshold :
  below_threshold_spec [10; 20; 1; 40; 9; 0; 0] 500 true.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.