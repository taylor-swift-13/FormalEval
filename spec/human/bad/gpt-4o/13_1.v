Require Import ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

(* Pre: at least one of `a` or `b` is non-zero (gcd(0,0) is undefined) *)
Definition problem_13_pre (a b : Z) : Prop :=
  a <> 0 \/ b <> 0.

Definition problem_13_spec (a b output : Z) : Prop :=
  (a mod output = 0) /\
  (b mod output = 0) /\
  (forall x : Z, (a mod x = 0) -> (b mod x = 0) -> x > 0 -> x <= output).

Definition greatest_common_divisor (a b : Z) : Z :=
  Z.gcd a b.

Example problem_13_test : greatest_common_divisor 3 7 = 1.
Proof.
  unfold greatest_common_divisor.
  simpl.
  reflexivity.
Qed.

(* Now, prove the test case meets the specification *)
Example problem_13_test_spec :
  problem_13_spec 3 7 (greatest_common_divisor 3 7).
Proof.
  unfold problem_13_spec.
  unfold greatest_common_divisor.
  simpl.
  split.
  - apply Z.gcd_divide_l.
  - split.
    + apply Z.gcd_divide_r.
    + intros x H1 H2 H3.
      apply Z.gcd_greatest.
      * exact H1.
      * exact H2.
      * exact H3.
Qed.