Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_530122_9877 :
  Spec 530122 9877 3166.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hcalc : (2 ^ 530122) mod 9877 = 3166).
  {
    (* Direct computation of the modulus using built-in functions *)
    vm_compute.
    reflexivity.
  }
  rewrite Hcalc.
  reflexivity.
Qed.