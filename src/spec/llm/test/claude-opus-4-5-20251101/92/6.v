Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition any_int_spec_real (x y z : R) (all_integers : bool) (result : bool) : Prop :=
  (all_integers = false -> result = false) /\
  (all_integers = true -> result = true <-> (x = y + z \/ y = x + z \/ z = y + x)).

Example test_any_int : any_int_spec_real (22/10) (22/10) (22/10) false false.
Proof.
  unfold any_int_spec_real.
  split.
  - intros _. reflexivity.
  - intros H. discriminate H.
Qed.