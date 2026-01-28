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

Example test_hex_key : hex_key_spec "1234567890ABCDEF12345BBAA22012345678900ABCDEFEA12345CACE1721234567890ABCDEF12345BBAA22012334567890ABCDEFA1234BB37137D1DDBCB1234567890ABCDEF12345BBAA2201234567890ABCDEFA12345BBAA202002EB3133A11DDCBC5BCEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118B872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200ADEADBBAA202002E" 166.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.