Require Import Nat.
Require Import Lia.

Definition largest_divisor_spec (n : nat) (result : nat) : Prop :=
  (result < n /\ n mod result = 0) /\ (forall x : nat, x < n -> n mod x = 0 -> x <= result).

Example test_largest_divisor_3 : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - split.
    + simpl. lia.
    + simpl. reflexivity.
  - intros x Hx Hmod.
    destruct x.
    + simpl in Hmod. discriminate.
    + destruct x.
      * lia.
      * destruct x.
        -- simpl in Hmod. discriminate.
        -- lia.
Qed.