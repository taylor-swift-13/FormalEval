Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\
    output = sum_digits p)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Example problem_94_test1 :
  problem_94_spec [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3] 10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  split.
  - repeat (try (left; reflexivity); right).
    reflexivity.
  - split.
    + (* Proving that 181 is prime *)
      apply prime_intro.
      * unfold Z.lt. simpl. lia.
      * unfold Z.divide. intros. destruct H as [k Hk].
        assert (Hk_cases : k = 1 \/ k = 181) by lia.
        destruct Hk_cases as [Hk1 | Hk181].
        -- left. assumption.
        -- right. rewrite Hk181 in Hk. simpl in Hk. lia.
    + split.
      * (* Proving 181 is the largest prime in the list *)
        intros p' Hp' Hp'_prime.
        destruct (Nat.eq_dec p' 181).
        -- lia.
        -- assert (p' < 181) by (apply Znumtheory.prime_above; assumption).
           lia.
      * (* Proving the output is the sum of the digits of 181 *)
        unfold sum_digits. unfold sum_digits_fueled.
        simpl. reflexivity.
Qed.