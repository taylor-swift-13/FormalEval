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

Example test_hex_key : hex_key_spec "275322022EBD73ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DD753CEEFAD753BDCEE753BDFCF0BDCE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0CEEFFBABBE753BDCE02067F89ADBCDEF0333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC5555A7F89ABCDEF002" 116.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.