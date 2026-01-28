Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory. 
Import ListNotations.
Open Scope nat_scope.

(* Auxiliary definition 2: Calculate sum of digits of a natural number (fueled) *)
Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* Fuel exhausted *)
  | S fuel' =>
    match n with
    | 0 => 0 (* n is 0 *)
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

(* Input list can contain any natural number *)
Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    (* 1. p must be in the list *)
    In p lst /\

    (* 2. p must be prime *)
    prime (Z.of_nat p) /\

    (* 3. p is the largest prime in the list *)
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\

    (* 4. output is the sum of digits of p *)
    output = sum_digits p)
  \/
  (* If no primes exist, output is 0 *)
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Example problem_94_test : problem_94_spec [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3] 10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  repeat split.
  - (* Goal 1: In 181 lst *)
    repeat (left; reflexivity || right).
  
  - (* Goal 2: prime (Z.of_nat 181) *)
    (* We use the decidability of primality from Znumtheory. *)
    let H := eval vm_compute in (prime_dec (Z.of_nat 181)) in
    match H with
    | left p => exact p
    | right _ => fail "181 should be prime"
    end.

  - (* Goal 3: forall p', In p' lst -> prime p' -> p' <= 181 *)
    intros p' Hin Hp'.
    simpl in Hin.
    (* Decompose the list membership hypothesis into individual cases *)
    repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           | [ H : False |- _ ] => contradiction
           end; subst.
    
    (* Try to solve p' <= 181 for all cases using arithmetic solver.
       This will solve all cases except p' = 324. *)
    all: try lia.
    
    (* For the remaining cases (where p' > 181, i.e., 324), we must prove they are not prime.
       Hp' asserts they are prime, so we derive a contradiction. *)
    all: exfalso.
    all: match goal with
         | [ H : prime (Z.of_nat ?n) |- _ ] =>
             let decision := eval vm_compute in (prime_dec (Z.of_nat n)) in
             match decision with
             | right np => apply np; exact H
             | left _ => fail 1 "Found a prime larger than 181 in the list!"
             end
         end.

  - (* Goal 4: 10 = sum_digits 181 *)
    vm_compute. reflexivity.
Qed.