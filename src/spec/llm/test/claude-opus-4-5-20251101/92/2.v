Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec 2.5 2 3 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros H. destruct H as [H | [H | H]]; lra.
Qed.