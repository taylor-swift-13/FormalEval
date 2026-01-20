Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.

Definition is_prime (p : nat) : Prop :=
  p > 1 /\ forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition factorize_spec (n : nat) (factors : list nat) : Prop :=
  fold_right mult 1 factors = n /\
  Forall is_prime factors /\
  Sorted le factors.

Lemma is_prime_via_Z : forall n, prime (Z.of_nat n) -> is_prime n.
Proof.
  intros n Hp.
  destruct Hp as [Hgt Hndiv].
  split.
  - apply Nat2Z.inj_lt. assumption.
  - intros d Hd.
    apply Nat2Z.inj_divide in Hd.
    destruct (Z.eq_dec (Z.of_nat d) 1) as [E1|NE1].
    { left. apply Nat2Z.inj. assumption. }
    destruct (Z.eq_dec (Z.of_nat d) (Z.of_nat n)) as [E2|NE2].
    { right. apply Nat2Z.inj. assumption. }
    exfalso.
    apply (Hndiv (Z.of_nat d)).
    + split.
      * assert (Z.of_nat d <> 0).
        { intro Hz. rewrite Hz in Hd. apply Z.divide_0_l in Hd.
          rewrite Hd in Hgt. lia. }
        lia.
      * assert (Z.of_nat d <= Z.of_nat n).
        { apply Nat2Z.inj_le. apply Nat.divide_pos_le.
          - intro Hn. rewrite Hn in Hgt. simpl in Hgt. lia.
          - apply Nat2Z.inj_divide. assumption. }
        lia.
    + assumption.
Qed.

Lemma fold_right_mul_Z : forall l,
  Z.of_nat (fold_right mult 1 l) = fold_right Z.mul 1%Z (map Z.of_nat l).
Proof.
  induction l; simpl; [reflexivity|].
  rewrite Nat2Z.inj_mul. rewrite IHl. reflexivity.
Qed.

Example test_factorize_large : factorize_spec (Z.to_nat 1073741790%Z) [2; 3; 5; 11; 47; 107; 647].
Proof.
  unfold factorize_spec.
  split.
  - apply Nat2Z.inj.
    rewrite fold_right_mul_Z.
    rewrite Z2Nat.id.
    + vm_compute. reflexivity.
    + vm_compute. discriminate.
  - split.
    + repeat constructor; apply is_prime_via_Z;
      match goal with
      | |- prime (Z.of_nat ?n) =>
          let b := eval vm_compute in (prime_dec (Z.of_nat n)) in
          match b with
          | left H => exact H
          | right _ => fail "Not prime"
          end
      end.
    + repeat constructor; try lia.
Qed.