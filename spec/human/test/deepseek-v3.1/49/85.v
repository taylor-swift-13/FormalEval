Require Import ZArith.
Open Scope Z_scope.

Definition problem_49_pre (n p : Z) : Prop := (n >= 0 /\ p > 0).

Definition problem_49_spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example test_modp : problem_49_spec 19 5 3.
Proof.
  unfold problem_49_spec.
  intro H.
  destruct H as [Hn Hp].
  simpl.
  compute.
  reflexivity.
Qed.