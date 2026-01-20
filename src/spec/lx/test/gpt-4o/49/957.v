Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_530122_523 :
  Spec 530122 523 376.
Proof.
  unfold Spec.
  intros [Hn Hp].
  replace (2 ^ 530122 mod 523) with 376.
  - reflexivity.
  - (* Explicit computation to resolve the modulo operation *)
    vm_compute. reflexivity.
Qed.