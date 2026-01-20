Require Import ZArith Lia.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example is_simple_power_spec_example_16_2_true :
  is_simple_power_spec 16%Z 2%Z true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 4%Z.
    split.
    + lia.
    + vm_compute; reflexivity.
  - intros _.
    reflexivity.
Qed.