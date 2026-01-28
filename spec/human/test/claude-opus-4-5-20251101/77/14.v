Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 512%Z true.
Proof.
  unfold problem_77_spec.
  split.
  - intros _.
    exists 8%Z.
    reflexivity.
  - intros _.
    reflexivity.
Qed.