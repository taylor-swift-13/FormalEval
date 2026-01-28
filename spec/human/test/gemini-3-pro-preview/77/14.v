Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_512 : problem_77_spec 512 true.
Proof.
  unfold problem_77_spec.
  split.
  - intros _.
    exists 8.
    reflexivity.
  - intros _.
    reflexivity.
Qed.