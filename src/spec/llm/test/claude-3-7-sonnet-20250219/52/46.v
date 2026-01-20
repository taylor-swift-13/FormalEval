Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => if Z.ltb x t then true else false) l.

Example test_below_threshold :
  below_threshold_spec [-1; -2; -4] (-4) false.
Proof.
  unfold below_threshold_spec.
  simpl.
  reflexivity.
Qed.