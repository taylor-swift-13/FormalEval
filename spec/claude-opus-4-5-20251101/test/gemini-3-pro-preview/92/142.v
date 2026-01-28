Require Import Reals.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Example test_any_int : any_int_spec (-122.24385010385771%R) (-123.7%R) (-123.04588347134523%R) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros [H | [H | H]]; lra.
Qed.