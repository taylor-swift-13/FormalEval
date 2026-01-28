Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.

Inductive sum_digits_fueled_rel : nat -> nat -> nat -> Prop :=
  | sdfr_zero_fuel : forall n, sum_digits_fueled_rel n 0 0
  | sdfr_zero_n : forall fuel, sum_digits_fueled_rel 0 fuel 0
  | sdfr_step : forall n fuel fuel' sum_tail,
      fuel = S fuel' ->
      n <> 0 ->
      sum_digits_fueled_rel (n / 10) fuel' sum_tail ->
      sum_digits_fueled_rel n fuel ((n mod 10) + sum_tail).

Inductive sum_digits_rel : nat -> nat -> Prop :=
  | sdr_base : forall n sum, sum_digits_fueled_rel n n sum -> sum_digits_rel n sum.

Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\
    sum_digits_rel p output)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Lemma prime_2 : prime (Z.of_nat 2).
Proof.
  rewrite Z2Nat.id; [apply prime_2|lia].
Qed.

Lemma prime_3 : prime (Z.of_nat 3).
Proof.
  rewrite Z2Nat.id; [constructor; try lia; intros n (H1, H2); assert (H : n = 1 \/ n = 3) by lia; destruct H; subst; auto|lia].
Qed.

Lemma prime_5 : prime (Z.of_nat 5).
Proof.
  rewrite Z2Nat.id; [constructor; try lia; intros n (H1, H2); assert (H : n = 1 \/ n = 5) by lia; destruct H; subst; auto|lia].
Qed.

Lemma prime_7 : prime (Z.of_nat 7).
Proof.
  rewrite Z2Nat.id; [constructor; try lia; intros n (H1, H2); assert (H : n = 1 \/ n = 7) by lia; destruct H; subst; auto|lia].
Qed.

Lemma prime_181 : prime (Z.of_nat 181).
Proof.
  rewrite Z2Nat.id; [constructor; try lia; intros n (H1, H2); assert (H : n = 1 \/ n = 181) by lia; destruct H; subst; auto|lia].
Qed.

Lemma sum_digits_181 : sum_digits_rel 181 10.
Proof.
  apply sdr_base.
  apply sdfr_step with (fuel' := 180).
  - reflexivity.
  - lia.
  - apply sdfr_step with (fuel' := 17).
    + reflexivity.
    + lia.
    + apply sdfr_step with (fuel' := 1).
      * reflexivity.
      * lia.
      * apply sdfr_step with (fuel' := 0).
        { reflexivity. }
        { lia. }
        { apply sdfr_zero_fuel. }
Qed.

Example test_case_1 : problem_94_spec 
  [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3] 10.
Proof.
  left. exists 181.
  repeat split.
  - unfold In; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
  - apply prime_181.
  - intros p' Hp' Hprime.
    destruct Hp' as [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 [|x11 [|x12 [|x13 [|x14 [|x15 [|x16 [|x17 [|x18 [|x19 [|x20 [|x21 [|x22]]]]]]]]]]]]]]]]]]]].
    + lia.
    + assert (x1 = 3) by auto; subst.
      rewrite Z2Nat.id; [apply prime_3|lia].
      lia.
    + assert (x2 = 2) by auto; subst.
      rewrite Z2Nat.id; [apply prime_2|lia].
      lia.
    + assert (x3 = 1) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x4 = 3) by auto; subst.
      rewrite Z2Nat.id; [apply prime_3|lia].
      lia.
    + assert (x5 = 5) by auto; subst.
      rewrite Z2Nat.id; [apply prime_5|lia].
      lia.
    + assert (x6 = 7) by auto; subst.
      rewrite Z2Nat.id; [apply prime_7|lia].
      lia.
    + assert (x7 = 4) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x8 = 5) by auto; subst.
      rewrite Z2Nat.id; [apply prime_5|lia].
      lia.
    + assert (x9 = 5) by auto; subst.
      rewrite Z2Nat.id; [apply prime_5|lia].
      lia.
    + assert (x10 = 5) by auto; subst.
      rewrite Z2Nat.id; [apply prime_5|lia].
      lia.
    + assert (x11 = 2) by auto; subst.
      rewrite Z2Nat.id; [apply prime_2|lia].
      lia.
    + assert (x12 = 181) by auto; subst.
      rewrite Z2Nat.id; [apply prime_181|lia].
      lia.
    + assert (x13 = 32) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x14 = 4) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x15 = 32) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x16 = 3) by auto; subst.
      rewrite Z2Nat.id; [apply prime_3|lia].
      lia.
    + assert (x17 = 2) by auto; subst.
      rewrite Z2Nat.id; [apply prime_2|lia].
      lia.
    + assert (x18 = 32) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x19 = 324) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x20 = 4) by auto; subst.
      unfold prime in Hprime.
      destruct Hprime as [Hpos Hdiv].
      simpl in Hpos.
      lia.
    + assert (x21 = 3) by auto; subst.
      rewrite Z2Nat.id; [apply prime_3|lia].
      lia.
    + contradiction.
  - apply sum_digits_181.
Qed.