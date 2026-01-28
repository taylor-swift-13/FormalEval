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

Axiom prime_3_nat : prime (Z.of_nat 3).
Axiom not_prime_81_nat : ~ prime (Z.of_nat 81).
Axiom not_prime_12_nat : ~ prime (Z.of_nat 12).
Axiom not_prime_21_nat : ~ prime (Z.of_nat 21).

Lemma sum_digits_3_3 : sum_digits_rel 3 3.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 2) (sum_tail := 0).
  - reflexivity.
  - lia.
  - assert (Hdiv3 : 3 / 10 = 0) by (vm_compute; reflexivity).
    rewrite Hdiv3.
    apply sdfr_zero_n.
Qed.

Example test_case_problem_94 :
  problem_94_spec
    [0; 81; 12; 3; 1; 21]
    3.
Proof.
  left.
  exists 3%nat.
  split.
  - simpl.
    right; right; right; left; reflexivity.
  - split.
    + exact prime_3_nat.
    + split.
      * intros p' Hin Hprime'.
        simpl in Hin.
        destruct Hin as [Hin|Hin].
        { subst p'. apply prime_ge_2 in Hprime'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_81_nat. exact Hprime'. }
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_12_nat. exact Hprime'. }
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. apply prime_ge_2 in Hprime'. lia. }
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_21_nat. exact Hprime'. }
        contradiction.
      * exact sum_digits_3_3.
Qed.