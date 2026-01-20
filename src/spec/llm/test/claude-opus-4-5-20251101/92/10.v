Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (result : bool) : Prop :=
  result = true <-> (x = y + z \/ y = x + z \/ z = y + x).

Definition any_int_spec_mixed (x : R) (y z : Z) (result : bool) : Prop :=
  result = false.

Example test_any_int : any_int_spec_mixed 3.0%R 4%Z 7%Z false.
Proof.
  unfold any_int_spec_mixed.
  reflexivity.
Qed.