Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 728 false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate.
  - intros [x H].
    nia.
Qed.