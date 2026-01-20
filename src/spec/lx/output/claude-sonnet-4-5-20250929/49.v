Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example test_modp :
  Spec 3 5 3.
Proof.
  unfold Spec.
  intro H.
  simpl.
  reflexivity.
Qed.