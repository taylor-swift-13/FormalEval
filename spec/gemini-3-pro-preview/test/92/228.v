Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (
    (exists n : Z, IZR n = x) /\
    (exists n : Z, IZR n = y) /\
    (exists n : Z, IZR n = z) /\
    (x = y + z \/ y = x + z \/ z = x + y)
  ).

Example test_any_int : any_int_spec (-122.41081028675096) (-123.04588347134523) (-63.928039388560606) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [_ [_ [_ [H | [H | H]]]]]; lra.
Qed.