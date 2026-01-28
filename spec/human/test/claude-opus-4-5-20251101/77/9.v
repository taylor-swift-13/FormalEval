Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_1728 : problem_77_spec 1728%Z true.
Proof.
  unfold problem_77_spec.
  split.
  - intros _.
    exists 12%Z.
    reflexivity.
  - intros _.
    reflexivity.
Qed.