Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_138_138_15 : problem_157_spec 138%Z 138%Z 15%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H; exfalso; discriminate H.
  - intros H; exfalso.
    destruct H as [H|H].
    + cbv in H. assert (38088 <> 225) by lia. congruence.
    + destruct H as [H|H].
      * cbv in H. assert (19269 <> 19044) by lia. congruence.
      * cbv in H. assert (19269 <> 19044) by lia. congruence.
Qed.