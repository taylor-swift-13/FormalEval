Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_case_1_2_3 : problem_157_spec 1 2 3 false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H.
    destruct H as [H | [H | H]].
    + (* 1*1 + 2*2 = 3*3 *) 
      compute in H. rewrite <- Z.mul_add_distr_r in H. 
      rewrite Z.mul_add_distr_r in H. 
      calc in H.
      discriminate H.
    + (* 1*1 + 3*3 = 2*2 *)
      compute in H. 
      rewrite <- Z.mul_add_distr_r in H.
      rewrite Z.mul_add_distr_r in H.
      calc in H.
      discriminate H.
    + (* 2*2 + 3*3 = 1*1 *) 
      compute in H.
      rewrite <- Z.mul_add_distr_r in H.
      rewrite Z.mul_add_distr_r in H.
      calc in H.
      discriminate H.
  - intros H.
    discriminate H.
Qed.