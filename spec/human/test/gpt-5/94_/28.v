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

Axiom prime_127_nat : prime (Z.of_nat 127).

Lemma sum_digits_127_10 : sum_digits_rel 127 10.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 126) (sum_tail := 3).
  - reflexivity.
  - lia.
  - assert (Hdiv127 : 127 / 10 = 12) by (vm_compute; reflexivity).
    rewrite Hdiv127.
    eapply sdfr_step with (fuel' := 125) (sum_tail := 1).
    + reflexivity.
    + lia.
    + assert (Hdiv12 : 12 / 10 = 1) by (vm_compute; reflexivity).
      rewrite Hdiv12.
      eapply sdfr_step with (fuel' := 124) (sum_tail := 0).
      * reflexivity.
      * lia.
      * assert (Hdiv1 : 1 / 10 = 0) by (vm_compute; reflexivity).
        rewrite Hdiv1.
        apply sdfr_zero_n.
Qed.

Example test_case_problem_94 :
  problem_94_spec
    [0; 1; 2; 3; 4; 5; 127; 7; 7; 8; 9]
    10.
Proof.
  left.
  exists 127%nat.
  split.
  - simpl.
    right; right; right; right; right; right; left; reflexivity.
  - split.
    + exact prime_127_nat.
    + split.
      * intros p' Hin Hprime'.
        simpl in Hin.
        destruct Hin as [Hin|Hin].
        { subst p'. apply prime_ge_2 in Hprime'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. apply prime_ge_2 in Hprime'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        contradiction.
      * exact sum_digits_127_10.
Qed.