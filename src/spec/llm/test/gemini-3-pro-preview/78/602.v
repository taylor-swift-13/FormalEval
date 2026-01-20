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

Example test_hex_key : hex_key_spec "753BD7ABCDEF202020CBAABBBBB333A11DDBC55A2022E753BDCEB2BCC22EEFFEEDDCCBBAACDF11118872159CEFF23BCC337312345B67CEEFAD890ABCDEF12345BBAA20200BBD4D" 72.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.