Require Import ZArith.
Require Import Lia.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_is_simple_power : is_simple_power_spec 16%Z 2%Z true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 4%Z.
    split.
    + lia.
    + reflexivity.
  - intros _. reflexivity.
Qed.