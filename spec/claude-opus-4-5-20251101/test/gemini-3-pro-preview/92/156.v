Require Import Reals.
Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <->
  ((exists (ix iy iz : Z), x = IZR ix /\ y = IZR iy /\ z = IZR iz) /\
   (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.7) (-123.7) (-123.7) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [_ [H | [H | H]]]; lra.
Qed.