Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_125 : problem_77_spec 125 true.
Proof.
  unfold problem_77_spec.
  split.
  - intros _.
    exists 5.
    reflexivity.
  - intros _.
    reflexivity.
Qed.