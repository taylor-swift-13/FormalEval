Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* Specification definitions provided in the prompt *)
Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

(* Test case: input = ["Hello"] -> length is 5 *)
(* We represent "Hello" as a list of ASCII values (nats) *)
Definition input_hello : list nat := [72; 101; 108; 108; 111].

Example test_prime_length_hello : prime_length_spec input_hello true.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  unfold input_hello.
  (* Calculate the length of the list *)
  simpl length.
  (* Evaluate the boolean expression for primality of 5 *)
  (* 5 is prime, so the result should be true *)
  vm_compute.
  reflexivity.
Qed.