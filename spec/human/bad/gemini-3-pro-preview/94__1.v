Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope nat_scope.

(* Specification definitions *)
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

(* Test Case *)
Definition test_lst : list nat := 
  [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3].

(* Tactics for solving primality *)
Ltac solve_prime :=
  match goal with
  | [ |- prime ?z ] =>
      let r := eval vm_compute in (prime_dec z) in
      match r with
      | left ?h => exact h
      | right _ => fail "Expected prime, found composite"
      end
  end.

Ltac solve_not_prime :=
  match goal with
  | [ |- ~ prime ?z ] =>
      let r := eval vm_compute in (prime_dec z) in
      match r with
      | right ?h => exact h
      | left _ => fail "Expected composite, found prime"
      end
  end.

Example problem_94_test : problem_94_spec test_lst 10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  repeat split.
  
  (* 1. Prove 181 is in the list *)
  - unfold test_lst.
    repeat (simpl; match goal with
                   | [ |- _ \/ _ ] => left; reflexivity
                   | [ |- _ \/ _ ] => right
                   end).
    contradiction.

  (* 2. Prove 181 is prime *)
  - solve_prime.

  (* 3. Prove 181 is the largest prime in the list *)
  - intros p' Hin Hp.
    unfold test_lst in Hin.
    (* We iterate through the list. For each element, we check if it is <= 181.
       If it is greater, we prove it is not prime to contradict Hp. *)
    repeat (
      destruct Hin as [H_eq | Hin];
      [ subst p';
        try (solve [lia]); (* Case: p' <= 181 *)
        (* Case: p' > 181. Must prove ~ prime p' to contradict Hp *)
        exfalso;
        assert (H_np: ~ prime (Z.of_nat p')) by solve_not_prime;
        apply H_np; assumption
      | 
        (* Continue to next element *)
      ]
    ).
    (* The repeat loop terminates when Hin is False (empty list), which destruct solves automatically. *)

  (* 4. Prove sum of digits of 181 is 10 *)
  - apply sdr_base.
    (* 181 -> 18 -> 1 -> 0 *)
    eapply sdfr_step. reflexivity. lia.
    eapply sdfr_step. reflexivity. lia.
    eapply sdfr_step. reflexivity. lia.
    apply sdfr_zero_n.
Qed.