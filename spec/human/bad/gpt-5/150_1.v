Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Definition problem_150_pre (n x y : nat) : Prop := True.

Definition problem_150_spec (n x y res : nat) : Prop :=
  (prime (Z.of_nat n) -> res = x) /\
  (~ prime (Z.of_nat n) -> res = y).

Open Scope Z_scope.

Example problem_150_test_example :
  problem_150_spec 7 34 12 34.
Proof.
  unfold problem_150_spec.
  split.
  - intros _. reflexivity.
  - intros Hnot.
    assert (prime (Z.of_nat 7)).
    { change (prime 7%Z).
      pose (d := prime_dec 7%Z (ltac:(lia))).
      vm_compute in d.
      inversion d; subst; auto.
    }
    contradiction.
Qed.