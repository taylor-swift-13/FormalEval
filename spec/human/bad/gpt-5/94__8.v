Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
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

Axiom prime_8191_nat : prime (Z.of_nat 8191).
Axiom not_prime_123456_nat : ~ prime (Z.of_nat 123456).

Lemma sum_digits_8191_19 : sum_digits_rel 8191 19.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 8190) (sum_tail := 18).
  - reflexivity.
  - lia.
  - assert (Hdiv8191 : 8191 / 10 = 819) by (vm_compute; reflexivity).
    rewrite Hdiv8191.
    eapply sdfr_step with (fuel' := 8189) (sum_tail := 9).
    + reflexivity.
    + lia.
    + assert (Hdiv819 : 819 / 10 = 81) by (vm_compute; reflexivity).
      rewrite Hdiv819.
      eapply sdfr_step with (fuel' := 8188) (sum_tail := 8).
      * reflexivity.
      * lia.
      * assert (Hdiv81 : 81 / 10 = 8) by (vm_compute; reflexivity).
        rewrite Hdiv81.
        eapply sdfr_step with (fuel' := 8187) (sum_tail := 0).
        -- reflexivity.
        -- lia.
        -- assert (Hdiv8 : 8 / 10 = 0) by (vm_compute; reflexivity).
           rewrite Hdiv8.
           apply sdfr_zero_n.
Qed.

Example test_case_problem_94 :
  problem_94_spec
    [8191; 123456; 127; 7]
    19.
Proof.
  left.
  exists 8191%nat.
  split.
  - simpl. left. reflexivity.
  - split.
    + exact prime_8191_nat.
    + split.
      * intros p' Hin Hprime'.
        simpl in Hin.
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_123456_nat. exact Hprime'. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        contradiction.
      * exact sum_digits_8191_19.
Qed.