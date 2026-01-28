Require Import Nat.
Require Import Lia.
Require Import ZArith.

Open Scope Z_scope.

Definition problem_60_pre (n : Z) : Prop := n > 0.

Definition problem_60_spec (n output: Z) : Prop :=
  2 * output = n*(n+1).

Example test_sum_to_n_1 : problem_60_spec 1000003 500003500006.
Proof.
  unfold problem_60_spec.
  reflexivity.
Qed.