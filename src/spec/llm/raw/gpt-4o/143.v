
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.PrimeNat.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime (n : nat) : bool :=
  negb (n <? 2 || existsb (fun x => n mod x =? 0) (seq 2 (Nat.sqrt n - 1))).

Definition words_in_sentence_spec (sentence : string) (result : string) : Prop :=
  let words := String.split " " sentence in
  let filtered_words := filter (fun word => is_prime (String.length word)) words in
  result = String.concat " " filtered_words.
