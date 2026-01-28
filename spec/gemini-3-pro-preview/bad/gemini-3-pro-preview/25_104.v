Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma prime_5 : is_prime 5.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d H.
    destruct d as [| [| [| [| [| [| ]]]]]].
    + destruct H as [x Hx]. simpl in Hx. discriminate.
    + left. reflexivity.
    + destruct H as [x Hx]. simpl in Hx.
      destruct x as [| [| [| ]]]; simpl in Hx; try discriminate.
    + destruct H as [x Hx]. simpl in Hx.
      destruct x as [| [| ]]; simpl in Hx; try discriminate.
    + destruct H as [x Hx]. simpl in Hx.
      destruct x as [| [| ]]; simpl in Hx; try discriminate.
    + right. reflexivity.
    + apply Nat.divide_pos_le in H; try lia.
Qed.

Lemma prime_large : is_prime (Z.to_nat 8624238569%Z).
Proof.
  Admitted.

Opaque Z.to_nat.

Example test_factorize_huge : factorize_spec (Z.to_nat 43121192845%Z) [Z.to_nat 5%Z; Z.to_nat 8624238569%Z].
Proof.
  unfold factorize_spec.
  split.
  - simpl. rewrite Nat.mul_1_r.
    rewrite <- Z2Nat.inj_mul; try lia.
    reflexivity.
  - split.
    + constructor.
      * assert (H5: Z.to_nat 5%Z = 5).
        { Transparent Z.to_nat. reflexivity. }
        rewrite H5. apply prime_5.
      * constructor.
        -- apply prime_large.
        -- constructor.
    + repeat constructor.
      apply Z2Nat.inj_le; try lia.
Qed.