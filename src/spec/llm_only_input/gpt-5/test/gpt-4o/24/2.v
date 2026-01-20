Require Import Nat.
Require Import Lia.
Require Import ZArith.

Definition largest_divisor_spec (n : nat) (result : nat) : Prop :=
  (result < n /\ n mod result = 0) /\ (forall x : nat, x < n -> n mod x = 0 -> x <= result).

Example largest_divisor_spec_7_1 : largest_divisor_spec 7 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - split.
    + lia.
    + simpl. reflexivity.
  - intros x Hlt Hmod.
    destruct x as [|x1].
    + lia.
    + destruct x1 as [|x2].
      * lia.
      * destruct x2 as [|x3].
        { simpl in Hmod. inversion Hmod. }
        { destruct x3 as [|x4].
          - simpl in Hmod. inversion Hmod.
          - destruct x4 as [|x5].
            + simpl in Hmod. inversion Hmod.
            + destruct x5 as [|x6].
              * simpl in Hmod. inversion Hmod.
              * destruct x6 as [|x7].
                { simpl in Hmod. inversion Hmod. }
                { exfalso. lia. } }
Qed.

Example largest_divisor_spec_Z_test_case :
  largest_divisor_spec (Z.to_nat 7%Z) (Z.to_nat 1%Z).
Proof.
  simpl.
  apply largest_divisor_spec_7_1.
Qed.