Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

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

Lemma prime_181 : prime 181.
Proof.
  apply prime_intro.
  - vm_compute. discriminate.
  - intros p [Hp1 Hp2].
    destruct (Zle_lt_or_eq p 1) as [Hle|Heq].
    + lia.
    + subst. lia.
    + vm_compute. intros [H1|[H2|[H3|H4]]]; lia.
Qed.

Lemma sum_digits_181 : sum_digits_rel 181 10.
Proof.
  apply sdr_base.
  remember 181 as n eqn:Heqn.
  assert (H: 181 = 1 * 100 + 8 * 10 + 1).
  { lia. }
  rewrite H.
  eapply sdfr_step.
  - reflexivity.
  - discriminate.
  - eapply sdfr_step.
    + reflexivity.
    + discriminate.
    + eapply sdfr_step.
      * reflexivity.
      * discriminate.
      * apply sdfr_zero_n.
Qed.

Example example_test_case_1 :
  problem_94_spec
    [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3]
    10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  split.
  - simpl. repeat (try (left; reflexivity); right).
  - split.
    + apply prime_181.
    + split.
      * intros p' HIn HPrime.
        destruct (Nat.eq_dec p' 181).
        { subst. lia. }
        simpl in HIn.
        repeat (try (destruct HIn as [HIn | HIn]; [subst; try lia |])); try contradiction.
        apply (prime_ge_2 _ HPrime). lia.
      * apply sum_digits_181.
Qed.