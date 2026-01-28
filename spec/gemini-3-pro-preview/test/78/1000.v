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

Example test_hex_key : hex_key_spec "1ABCDF11118872159CEFF23BCCBBDDDBBCFFEEDDCCBBBAA20200DDBBBCF753BDCEEFAD2020123BB1B1ABCD2020DDBBCC22EEFFEEDDBCCBBAA3133A11DDBC456789ABCDEF0FEEDDCCBBAA890ABCEAD0CDEFA12345BBAA20200" 79.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.