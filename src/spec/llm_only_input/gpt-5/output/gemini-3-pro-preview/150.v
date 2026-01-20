Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.

Open Scope Z_scope.

Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

Example x_or_y_spec_test : prime 7 -> x_or_y_spec 7 34 12 34.
Proof.
  intro Hp.
  unfold x_or_y_spec.
  split; [intros; reflexivity | intro Hnp; exfalso; apply Hnp; exact Hp].
Qed.

Example x_or_y_spec_test_output : prime 7 -> forall res, x_or_y_spec 7 34 12 res -> res = 34.
Proof.
  intros Hp res Hspec.
  destruct Hspec as [Hprime _].
  apply Hprime; exact Hp.
Qed.