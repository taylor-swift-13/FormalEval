Require Import ZArith.
Require Import Reals.
Require Import Bool.
Require Import Psatz.
Require Import Lra.

Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.7) (-123.7) (-123.04588347134523) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. inversion H.
  - intros [_ [_ [_ H]]].
    destruct H as [H | [H | H]]; lra.
Qed.