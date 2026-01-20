
Require Import List.
Require Import String.
Require Import ZArith.
Require Import Ascii.

Definition is_prime (a : nat) : bool :=
  match a with
  | O => false
  | S O => false
  | S (S _) as n => 
      let sqrt_n := Z.to_nat (Z.sqrt (Z.of_nat n)) in
      negb (existsb (fun x => Nat.eqb (n mod x) 0) (seq 2 (sqrt_n - 1)))
  end.

Definition words_in_sentence_spec (sentence : string) (result : string) : Prop :=
  let words := String.split " " sentence in
  let prime_words := filter (fun word => is_prime (String.length word)) words in
  result = String.concat " " prime_words.
