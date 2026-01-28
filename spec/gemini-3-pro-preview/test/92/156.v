Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists n : Z, IZR n = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.7) (-123.7) (-123.7) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [_ [_ [_ H]]].
    lra.
Qed.