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

Example test_hex_key : hex_key_spec "12345ACDF12345B67C2022EEEFAD890AB123ABB333A11DDBCBCD123456753BD7890ABCDEF12345BBAA20200EF202020CBAABBB2BB333CA11DDBC5555D4567CEEFAD22022E890ABCDEF12345BBAA200" 80.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.