Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char
  | "B"%char | "D"%char => true
  | _ => false
  end.

Fixpoint count_prime_hex (s : string) : nat :=
  match s with
  | "" => 0
  | String h t =>
    (if is_prime_hex_digit h then 1 else 0) +
    count_prime_hex t
  end.

Definition hex_key_impl (s : string) : nat :=
  count_prime_hex s.

Definition problem_78_pre (s : string) : Prop := True.

Definition problem_78_spec (s : string) (output : nat) : Prop :=
  output = hex_key_impl s.

Example test_753BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0 :
  problem_78_spec "753BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" 23.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.

  unfold is_prime_hex_digit.
  simpl. (* '7' is prime -> 1 + count_prime_hex "53BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)
  
  unfold is_prime_hex_digit.
  simpl. (* '5' is prime -> 1 + count_prime_hex "3BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)
  
  unfold is_prime_hex_digit.
  simpl. (* '3' is prime -> 1 + count_prime_hex "BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)
  
  unfold is_prime_hex_digit.
  simpl. (* 'B' is prime -> 1 + count_prime_hex "DCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)
  
  unfold is_prime_hex_digit.
  simpl. (* 'D' is prime -> 1 + count_prime_hex "CE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)
  
  unfold is_prime_hex_digit.
  simpl. (* 'C' not prime -> 0 + count_prime_hex "E0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'E' not prime -> 0 + count_prime_hex "0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '0' not prime -> 0 + count_prime_hex "201234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '2' is prime -> 1 + count_prime_hex "01234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '0' not prime -> 0 + count_prime_hex "1234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '1' not prime -> 0 + count_prime_hex "234567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '2' is prime -> 1 + count_prime_hex "34567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '3' is prime -> 1 + count_prime_hex "4567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '4' not prime -> 0 + count_prime_hex "567F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '5' is prime -> 1 + count_prime_hex "67F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '6' not prime -> 0 + count_prime_hex "7F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '7' is prime -> 1 + count_prime_hex "F89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'F' not prime -> 0 + count_prime_hex "89ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '8' not prime -> 0 + count_prime_hex "9ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '9' not prime -> 0 + count_prime_hex "ADBCDEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'A' not prime -> 0 + count_prime_hex "DBCEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'D' is prime -> 1 + count_prime_hex "BCEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'B' is prime -> 1 + count_prime_hex "CEF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'C' not prime -> 0 + count_prime_hex "EF753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'E' not prime -> 0 + count_prime_hex "F753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'F' not prime -> 0 + count_prime_hex "753BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '7' is prime -> 1 + count_prime_hex "53BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '5' is prime -> 1 + count_prime_hex "3BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '3' is prime -> 1 + count_prime_hex "BDCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'B' is prime -> 1 + count_prime_hex "DCE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'D' is prime -> 1 + count_prime_hex "CE02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'C' not prime -> 0 + count_prime_hex "E02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'E' not prime -> 0 + count_prime_hex "02067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '0' not prime -> 0 + count_prime_hex "2067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '2' is prime -> 1 + count_prime_hex "067F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '0' not prime -> 0 + count_prime_hex "67F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '6' not prime -> 0 + count_prime_hex "7F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '7' is prime -> 1 + count_prime_hex "F89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'F' not prime -> 0 + count_prime_hex "89ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '8' not prime -> 0 + count_prime_hex "9ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* '9' not prime -> 0 + count_prime_hex "ADBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'A' not prime -> 0 + count_prime_hex "DBCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'D' is prime -> 1 + count_prime_hex "BCDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'B' is prime -> 1 + count_prime_hex "CDEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'C' not prime -> 0 + count_prime_hex "DEF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'D' is prime -> 1 + count_prime_hex "EF0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'E' not prime -> 0 + count_prime_hex "F0" *)

  unfold is_prime_hex_digit.
  simpl. (* 'F' not prime -> 0 + count_prime_hex "0" *)

  unfold is_prime_hex_digit.
  simpl. (* '0' not prime -> 0 + count_prime_hex "" *)

  simpl.
  reflexivity.
Qed.