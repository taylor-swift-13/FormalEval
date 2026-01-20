Require Import List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition below_threshold_Z_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = forallb (fun x => Z.ltb x t) l.

Example test_below_threshold_Z :
  below_threshold_Z_spec [-1; 8; -2; 8] (-2) false.
Proof.
  unfold below_threshold_Z_spec.
  simpl.
  reflexivity.
Qed.