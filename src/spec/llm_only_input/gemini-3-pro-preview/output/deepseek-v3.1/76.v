Require Import ZArith.
Require Import Lia.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_is_simple_power : is_simple_power_spec 16%Z 2%Z true.
Proof.
  unfold is_simple_power_spec.
  split.
  - (* -> direction: Assume result=true, prove existence of k *)
    intros _.
    exists 4%Z.
    split.
    + (* Prove 0 <= 4 *)
      lia.
    + (* Prove 2^4 = 16 *)
      simpl.
      reflexivity.
  - (* <- direction: Assume existence of k, prove result=true *)
    intros _.
    reflexivity.
Qed.