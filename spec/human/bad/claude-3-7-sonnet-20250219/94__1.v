Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

(* Definitions from specification *)

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

(* sum_digits_fueled_rel helper to compute sum of digits *)

Fixpoint sum_digits (n : nat) : nat :=
  match n with
  | 0 => 0
  | _ => n mod 10 + sum_digits (n / 10)
  end.

(* Prove that sum_digits_fueled_rel n n (sum_digits n) *)

Lemma sum_digits_fueled_rel_correct:
  forall n, sum_digits_fueled_rel n n (sum_digits n).
Proof.
  induction n using nat_ind2; simpl.
  - (* n=0 *) apply sdfr_zero_n.
  - (* n > 0 *)
    apply sdfr_step with (fuel' := n).
    + reflexivity.
    + lia.
    + apply IHn.
Qed.

Lemma sum_digits_rel_correct:
  forall n, sum_digits_rel n (sum_digits n).
Proof.
  intros n.
  apply sdr_base.
  apply sum_digits_fueled_rel_correct.
Qed.

(* Define the test input *)

Definition test_list :=
  [0;3;2;1;3;5;7;4;5;5;5;2;181;32;4;32;3;2;32;324;4;3].

(* Prove primality of 181 *)

Lemma prime_181 : prime (Z.of_nat 181).
Proof.
  apply prime_intro; [lia|].
  intros d Hdiv.
  destruct (Z.eq_dec d 1) as [->| Hn1]; [lia|].
  destruct (Z.eq_dec d (Z.of_nat 181)) as [->| Hneq]; [lia|].
  simpl in Hdiv.
  apply Z.divide_lt_is_unit in Hdiv; auto with zarith.
Qed.

(* Primality of small primes in list *)

Lemma prime_2 : prime (Z.of_nat 2).
Proof. vm_compute; lia. Qed.

Lemma prime_3 : prime (Z.of_nat 3).
Proof. vm_compute; lia. Qed.

Lemma prime_5 : prime (Z.of_nat 5).
Proof. vm_compute; lia. Qed.

Lemma prime_7 : prime (Z.of_nat 7).
Proof. vm_compute; lia. Qed.

(* Prove that 181 is max prime in the list *)

Lemma max_prime_181:
  forall p,
    In p test_list ->
    prime (Z.of_nat p) ->
    p <= 181.
Proof.
  intros p HIn Hprime.
  destruct (Nat.eq_dec p 181) as [ -> | Hpneq ]; lia.
  (* Check the small primes in the list *)
  assert (p = 2 \/ p = 3 \/ p = 5 \/ p = 7).
  {
    (* Only these primes appear except 181 *)
    repeat (try (left; reflexivity); right).
    simpl in HIn.
    repeat match goal with
    | [ H : In ?x _ |- _ ] => simpl in H; destruct H as [Heq|Hrest]
    end.
    all: try discriminate.
  }
  destruct H as [H2 | [H3 | [H5 | H7]]]; subst; lia.
Qed.

(* 181 is in the test list *)

Lemma in_181: In 181 test_list.
Proof. simpl. reflexivity. Qed.

(* Now the full example proof *)

Example problem_94_test_1:
  problem_94_spec test_list 10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  repeat split.
  - apply in_181.
  - apply prime_181.
  - apply max_prime_181.
  - apply sum_digits_rel_correct.
Qed.