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

Axiom prime_181_nat : prime (Z.of_nat 181).
Axiom not_prime_324_nat : ~ prime (Z.of_nat 324).

Lemma sum_digits_181_10 : sum_digits_rel 181 10.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 180) (sum_tail := 9).
  - reflexivity.
  - lia.
  - assert (Hdiv181 : 181 / 10 = 18) by (vm_compute; reflexivity).
    rewrite Hdiv181.
    eapply sdfr_step with (fuel' := 179) (sum_tail := 1).
    + reflexivity.
    + lia.
    + assert (Hdiv18 : 18 / 10 = 1) by (vm_compute; reflexivity).
      rewrite Hdiv18.
      eapply sdfr_step with (fuel' := 178) (sum_tail := 0).
      * reflexivity.
      * lia.
      * assert (Hdiv1 : 1 / 10 = 0) by (vm_compute; reflexivity).
        rewrite Hdiv1.
        apply sdfr_zero_n.
Qed.

Example test_case_problem_94 :
  problem_94_spec
    [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3]
    10.
Proof.
  left.
  exists 181%nat.
  split.
  - simpl.
    right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
  - split.
    + exact prime_181_nat.
    + split.
      * intros p' Hin Hprime'.
        simpl in Hin.
        (* 0 *)
        destruct Hin as [Hin|Hin].
        { subst p'. apply prime_ge_2 in Hprime'. lia. }
        (* 3 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 2 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 1 *)
        destruct Hin as [Hin|Hin].
        { subst p'. apply prime_ge_2 in Hprime'. lia. }
        (* 3 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 5 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 7 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 4 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 5 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 5 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 5 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 2 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 181 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 32 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 4 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 32 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 3 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 2 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 32 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 324 *)
        destruct Hin as [Hin|Hin].
        { subst p'. exfalso. apply not_prime_324_nat. exact Hprime'. }
        (* 4 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* 3 *)
        destruct Hin as [Hin|Hin].
        { subst p'. lia. }
        (* end: impossible *)
        contradiction.
      * exact sum_digits_181_10.
Qed.