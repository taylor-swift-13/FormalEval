Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Example test_factorize_100 : factorize_spec 100 [2; 2; 5; 5].
Proof.
  unfold factorize_spec.
  split.
  - simpl. reflexivity.
  - split.
    + repeat constructor.
      * unfold is_prime. split; [lia |].
        intros d H.
        destruct d as [| [| [| d'] ]].
        -- destruct H as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
        -- left. reflexivity.
        -- right. reflexivity.
        -- apply Nat.divide_pos_le in H; lia.
      * unfold is_prime. split; [lia |].
        intros d H.
        destruct d as [| [| [| d'] ]].
        -- destruct H as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
        -- left. reflexivity.
        -- right. reflexivity.
        -- apply Nat.divide_pos_le in H; lia.
      * unfold is_prime. split; [lia |].
        intros d H.
        destruct d as [| [| [| [| [| [| d'] ]]]]]].
        -- destruct H as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
        -- left. reflexivity.
        -- exfalso. destruct H as [k Hk].
           assert (k < 3) by lia.
           repeat (destruct k; [simpl in Hk; try discriminate; lia | ]). lia.
        -- exfalso. destruct H as [k Hk].
           assert (k < 2) by lia.
           repeat (destruct k; [simpl in Hk; try discriminate; lia | ]). lia.
        -- exfalso. destruct H as [k Hk].
           assert (k < 2) by lia.
           repeat (destruct k; [simpl in Hk; try discriminate; lia | ]). lia.
        -- right. reflexivity.
        -- apply Nat.divide_pos_le in H; lia.
      * unfold is_prime. split; [lia |].
        intros d H.
        destruct d as [| [| [| [| [| [| d'] ]]]]]].
        -- destruct H as [z Hz]. rewrite Nat.mul_0_r in Hz. discriminate.
        -- left. reflexivity.
        -- exfalso. destruct H as [k Hk].
           assert (k < 3) by lia.
           repeat (destruct k; [simpl in Hk; try discriminate; lia | ]). lia.
        -- exfalso. destruct H as [k Hk].
           assert (k < 2) by lia.
           repeat (destruct k; [simpl in Hk; try discriminate; lia | ]). lia.
        -- exfalso. destruct H as [k Hk].
           assert (k < 2) by lia.
           repeat (destruct k; [simpl in Hk; try discriminate; lia | ]). lia.
        -- right. reflexivity.
        -- apply Nat.divide_pos_le in H; lia.
    + repeat (constructor; try lia).
Qed.