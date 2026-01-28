Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition fruit_distribution_spec (apples : Z) (oranges : Z) (n : Z) (result : Z) : Prop :=
  apples >= 0 /\
  oranges >= 0 /\
  n >= 0 /\
  n - apples - oranges >= 0 /\
  result = n - apples - oranges.

Example fruit_distribution_test_case : fruit_distribution_spec 97 1 200 102.
Proof.
  unfold fruit_distribution_spec.
  repeat split; lia.
Qed.