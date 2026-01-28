Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-122.24385010385771) (-123.7) (-123.04588347134523) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    discriminate.
  - intros [_ [_ [_ [H | [H | H]]]]]; lra.
Qed.