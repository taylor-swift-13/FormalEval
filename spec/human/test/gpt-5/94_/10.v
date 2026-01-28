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

Axiom prime_7_nat : prime (Z.of_nat 7).
Axiom not_prime_8_nat : ~ prime (Z.of_nat 8).
Axiom not_prime_9_nat : ~ prime (Z.of_nat 9).

Lemma sum_digits_7_7 : sum_digits_rel 7 7.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 6) (sum_tail := 0).
  - reflexivity.
  - lia.
  - assert (Hdiv7 : 7 / 10 = 0) by (vm_compute; reflexivity).
    rewrite Hdiv7.
    apply sdfr_zero_n.
Qed.

Example test_case_problem_94 :
  problem_94_spec
    [1; 2; 3; 4; 5; 6; 7; 8; 9]
    7.
Proof.
  left.
  exists 7%nat.
  split.
  - simpl.
    right; right; right; right; right; right; left; reflexivity.
  - split.
    + exact prime_7_nat.
    + split.
      * intros p' Hin Hprime'.
        simpl in Hin.
        (* 1 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 2 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 3 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 4 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 5 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 6 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 7 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 8 *)
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_8_nat. exact Hprime'. }
        (* 9 *)
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_9_nat. exact Hprime'. }
        (* end: impossible *)
        contradiction.
      * exact sum_digits_7_7.
Qed.