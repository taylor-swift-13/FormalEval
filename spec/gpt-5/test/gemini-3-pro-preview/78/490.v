Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition prime_hex_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 50 || Nat.eqb n 51 || Nat.eqb n 53 || Nat.eqb n 55 || Nat.eqb n 66 || Nat.eqb n 68.

Fixpoint count_prime_hex (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => Nat.add (if prime_hex_digit c then 1 else 0) (count_prime_hex rest)
  end.

Definition hex_key_spec (num : string) (count : nat) : Prop :=
  count = count_prime_hex num.

Example test_hex_key_long : hex_key_spec "77532202F2EBDC2022E753BDCEE7711BABCD2020DDB2BCC22EEFFEEDDCCBBAAEEFFA7F9ABCDEF033753BDCEEFFA7753BDCEEFAD2020123456789ABCDEABCD11ACD2020DDBB12345B67C2022EEEFAD890ABCD1234567890ABCDEF12345BBAA20200EF12345BBBBAAABDBC555ABBBDDDDDDCCCCC1111122222333334444455555F0F89ABCDEF0" 133.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.