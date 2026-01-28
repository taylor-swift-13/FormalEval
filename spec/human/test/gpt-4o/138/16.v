Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_pre (n : Z) : Prop := True.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example test_case_48 : problem_138_spec 48 true.
Proof.
  unfold problem_138_spec.
  split.
  - intros.
    exists 2, 4, 6, 36.
    repeat split; unfold is_positive_even; try (exists 1; lia);
    try (exists 2; lia); try (exists 3; lia); try (exists 18; lia).
  - intros [e1 [e2 [e3 [e4 [H1 [H2 [H3 [H4 Heq]]]]]]]].
    reflexivity.
Qed.