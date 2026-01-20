
Require Import ZArith.
Require Import List.
Require Import Bool.

Definition is_palindrome (n : Z) : bool :=
  let s := Z.to_string n in
  (s == rev s).

Definition even_odd_palindrome_spec (n : Z) (result : Z * Z) : Prop :=
  (1 <= n <= 1000)%Z /\
  let (even_cnt, odd_cnt) := result in
  even_cnt = Z.of_nat (length (filter (fun x => Z.even x = true) (filter is_palindrome (seq_Z 1 n)))) /\
  odd_cnt = Z.of_nat (length (filter (fun x => Z.even x = false) (filter is_palindrome (seq_Z 1 n)))).
