Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.04588347134523) (-63.928039388560606) (-122.485440891432) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros [_ [_ [_ [H | [H | H]]]]]; lra.
Qed.