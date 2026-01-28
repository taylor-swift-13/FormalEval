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

Axiom prime_139_nat : prime (Z.of_nat 139).
Axiom not_prime_112_nat : ~ prime (Z.of_nat 112).

Lemma sum_digits_139_13 : sum_digits_rel 139 13.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 138) (sum_tail := 4).
  - reflexivity.
  - lia.
  - assert (Hdiv139 : 139 / 10 = 13) by (vm_compute; reflexivity).
    rewrite Hdiv139.
    eapply sdfr_step with (fuel' := 137) (sum_tail := 1).
    + reflexivity.
    + lia.
    + assert (Hdiv13 : 13 / 10 = 1) by (vm_compute; reflexivity).
      rewrite Hdiv13.
      eapply sdfr_step with (fuel' := 136) (sum_tail := 0).
      * reflexivity.
      * lia.
      * assert (Hdiv1 : 1 / 10 = 0) by (vm_compute; reflexivity).
        rewrite Hdiv1.
        apply sdfr_zero_n.
Qed.

Example test_case_problem_94 :
  problem_94_spec
    [3; 101; 103; 107; 109; 112; 127; 131; 139]
    13.
Proof.
  left.
  exists 139%nat.
  split.
  - simpl.
    right; right; right; right; right; right; right; right; left; reflexivity.
  - split.
    + exact prime_139_nat.
    + split.
      * intros p' Hin Hprime'.
        simpl in Hin.
        (* 3 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 101 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 103 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 107 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 109 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 112 *)
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_112_nat. exact Hprime'. }
        (* 127 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 131 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 139 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* end: impossible *)
        contradiction.
      * exact sum_digits_139_13.
Qed.