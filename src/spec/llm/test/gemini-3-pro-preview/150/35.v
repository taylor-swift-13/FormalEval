Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

Example test_x_or_y_6 : x_or_y_spec 6 100 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H.
    reflexivity.
  - intros H.
    reflexivity.
Qed.