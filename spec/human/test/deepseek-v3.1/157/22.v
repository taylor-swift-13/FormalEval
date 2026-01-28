Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_case_15_17_6 : problem_157_spec 15 17 6 false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    destruct H as [H1 | [H2 | H3]].
    + compute in H1.
      discriminate H1.
    + compute in H2.
      discriminate H2.
    + compute in H3.
      discriminate H3.
Qed.