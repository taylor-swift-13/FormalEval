Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example problem_97_example : problem_97_spec (-9876543211) (-975312470) 0.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.