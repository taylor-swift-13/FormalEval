Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_530122_9878 :
  Spec 530122 9878 6758.
Proof.
  unfold Spec.
  intros [Hn Hp].
  replace (2 ^ 530122 mod 9878) with 6758%Z.
  reflexivity.
  (* Computation step to verify the modulo result *)
  vm_compute.
  reflexivity.
Qed.