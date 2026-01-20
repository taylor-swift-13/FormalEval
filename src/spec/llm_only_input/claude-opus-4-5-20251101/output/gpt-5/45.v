Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition triangle_area_spec (a h area : R) : Prop :=
  area = Rdiv (Rmult a h) (INR 2).

Example triangle_area_test : triangle_area_spec 5 3 7.5.
Proof.
  unfold triangle_area_spec.
  unfold Rdiv.
  simpl (INR 2).
  lra.
Qed.