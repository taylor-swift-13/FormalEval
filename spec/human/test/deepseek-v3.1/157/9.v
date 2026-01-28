Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_case_48_55_73 : problem_157_spec 48 55 73 true.
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