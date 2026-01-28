Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_case_10_6_8 : problem_157_spec 10 6 8 true.
Proof.
  unfold problem_157_spec.
  split.
  - intros H.
    right.
    right.
    compute.
    reflexivity.
  - intros H.
    destruct H as [H | [H | H]].
    + (* a * a + b * b = c * c *)
      compute in H.
      (* check if 10^2 + 6^2 = 8^2 *)
      rewrite Z.mul_assoc in H at 1.
      rewrite Z.pow2_mul in H.
      rewrite Z.mul_assoc in H at 2.
      rewrite Z.pow2_mul in H.
      rewrite Z.pow2_mul in H.
      change (100 + 36 = 64) in H.
      discriminate H.
    + (* a * a + c * c = b * b *)
      compute in H.
      (* check if 10^2 + 8^2 = 6^2 *)
      rewrite Z.pow2_mul in H.
      rewrite Z.pow2_mul in H.
      change (100 + 64 = 36) in H.
      discriminate H.
    + (* b * b + c * c = a * a *)
      compute in H.
      (* check if 6^2 + 8^2 = 10^2 *)
      rewrite Z.pow2_mul in H.
      rewrite Z.pow2_mul in H.
      change (36 + 64 = 100) in H.
      reflexivity.
Qed.