Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_65_10001_2022 : problem_157_spec 65%Z 10001%Z 2022%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. inversion H.
  - intros H.
    cbv in H.
    destruct H as [H|[H|H]]; exfalso.
    + assert (100024226 <> 4088484)%Z by lia. now apply H0.
    + assert (4092709 <> 100020001)%Z by lia. now apply H0.
    + assert (104108485 <> 4225)%Z by lia. now apply H0.
Qed.