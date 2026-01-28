Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Lemma prime_nat_prime_Z : forall (p : nat), prime p -> prime (Z.of_nat p).
Proof.
  intros p Hprime.
  apply prime_intro.
  - apply Z.gt_lt. rewrite Z2Nat.id by (apply Nat.le_0_l). 
    destruct (prime_ge_2 p Hprime); omega.
  - intros a b Hdiv.
    rewrite Z2Nat.id in Hdiv by (apply Nat.le_0_l).
    destruct (Z.eq_dec (Z.of_nat p) 1).
    + exfalso. apply prime_ge_2 in Hprime. omega.
    + destruct (prime_divisors _ Hprime _ (Z.divide_nat _ _ Hdiv)) as [[H|H]|H].
      * left. rewrite <- Z2Nat.inj_divide; try lia.
        apply Z.divide_antisym; assumption.
      * right. rewrite <- Z2Nat.inj_divide; try lia.
        apply Z.divide_antisym; assumption.
Qed.

Lemma Zprime_nat_prime : forall (p : nat), prime (Z.of_nat p) -> prime p.
Proof.
  intros p Hprime.
  apply prime_intro.
  - destruct (prime_ge_2 _ Hprime) as [Hp|Hp].
    + rewrite <- Nat2Z.inj_lt. apply Z.gt_lt in Hp. assumption.
    + inversion Hp.
  - intros a b Hdiv.
    assert (Hdiv' : (Z.of_nat p | Z.of_nat (a * b))).
    { rewrite Nat2Z.inj_mul. apply Z.divide_mul_r. exists (Z.of_nat a). reflexivity. }
    destruct (prime_divisors _ Hprime _ Hdiv') as [[H|H]|H].
    + left. apply Nat2Z.inj in H. rewrite Nat.mul_1_r in H. assumption.
    + right. apply Nat2Z.inj in H. rewrite Nat.mul_comm in H. rewrite Nat.mul_1_r in H. assumption.
Qed.

Definition problem_96_pre (n : nat) : Prop := True.

Definition problem_96_spec (n : nat) (result : list nat) : Prop :=
  (forall p, In p result -> prime (Z.of_nat p)) /\
  (forall p, In p result -> p < n) /\
  (forall p, prime (Z.of_nat p) -> p < n -> In p result) /\
  Sorted lt result /\
  NoDup result.

Lemma prime_2 : prime 2.
Proof.
  apply prime_intro; try split; try lia.
  intros n Hdiv.
  destruct (Nat.eq_dec n 1).
  - left; auto.
  - right.
    assert (n = 2) by (destruct n; try lia; destruct n; auto; lia).
    auto.
Qed.

Lemma prime_3 : prime 3.
Proof.
  apply prime_intro; try split; try lia.
  intros n Hdiv.
  destruct (Nat.eq_dec n 1).
  - left; auto.
  - right.
    assert (n = 3) by (destruct n; try lia; destruct n; try lia; destruct n; auto; lia).
    auto.
Qed.

Lemma Zprime_2 : prime (Z.of_nat 2).
Proof. apply prime_nat_prime_Z. apply prime_2. Qed.

Lemma Zprime_3 : prime (Z.of_nat 3).
Proof. apply prime_nat_prime_Z. apply prime_3. Qed.

Example test_case_5 : problem_96_spec 5 [2; 3].
Proof.
  unfold problem_96_spec.
  repeat split.
  - intros p H. simpl in H. destruct H as [H|H].
    + subst p. apply Zprime_2.
    + destruct H as [H|H].
      * subst p. apply Zprime_3.
      * contradiction.
  - intros p H. simpl in H. destruct H as [H|H].
    + subst p. lia.
    + destruct H as [H|H].
      * subst p. lia.
      * contradiction.
  - intros p Hprime Hlt.
    assert (Hprime_nat : prime p) by (apply Zprime_nat_prime; assumption).
    assert (Hp_ge_2 : p >= 2) by (apply prime_ge_2; assumption).
    destruct p as [|p].
    + lia.
    + destruct p as [|p].
      * lia.
      + destruct p as [|p].
        * simpl. left. reflexivity.  (* p = 2 *)
        + destruct p as [|p].
          * simpl. right. left. reflexivity.  (* p = 3 *)
          + simpl in Hlt. lia.  (* p >= 4, but p < 5, so p = 4 (not prime) *)
  - constructor.
    + constructor.
    + constructor; [lia|constructor].
  - constructor; [lia|constructor; [lia|constructor]].
Qed.