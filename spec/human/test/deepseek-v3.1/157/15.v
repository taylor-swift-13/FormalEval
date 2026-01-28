Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_case_8_15_17 : problem_157_spec 8 15 17 true.
Proof.
  unfold problem_157_spec.
  split.
  - intros H.
    left.
    compute.
    reflexivity.
  - intros H.
    reflexivity.
Qed.