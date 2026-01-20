Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Open Scope string_scope.
Open Scope char_scope.

Definition is_prime_hex (c : ascii) : bool :=
  match c with
  | "2" => true
  | "3" => true
  | "5" => true
  | "7" => true
  | "B" => true
  | "D" => true
  | _ => false
  end.

Fixpoint count_primes (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => 
      (if is_prime_hex c then 1 else 0) + count_primes rest
  end.

Definition hex_key_spec (num : string) (count : nat) : Prop :=
  count = count_primes num.

Example test_hex_key : hex_key_spec "CE73ABB333A11DDBCBCDEF202011ACD2020DDBB12345B67C2022EEEFAD890ABCDE12345B67C2022EEEFAD890ABCFDEF275373ABB3033A11DDBCBCDEF202020CBAABBB2BB333CA11D0DBC5555EF002AB4CDEF202020CBAABBBDDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BBAA2020033444555555E12345BBAA20200F12345BBBBAA20CBAABBB2BB333CA11DDEFEAD" 148.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.