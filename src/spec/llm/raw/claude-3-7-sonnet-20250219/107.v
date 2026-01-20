
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint string_reverse (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => append (string_reverse rest) (String c EmptyString)
  end.

Definition is_palindrome (n : nat) : bool :=
  let s := string_of_nat n in
  String.eqb s (string_reverse s).

Definition even_odd_palindrome_spec (n even_cnt odd_cnt : nat) : Prop :=
  1 <= n <= 1000 /\
  even_cnt = length (filter (fun x => negb (x mod 2 =? 1) && is_palindrome x) (seq 1 n)) /\
  odd_cnt = length (filter (fun x => (x mod 2 =? 1) && is_palindrome x) (seq 1 n)).
