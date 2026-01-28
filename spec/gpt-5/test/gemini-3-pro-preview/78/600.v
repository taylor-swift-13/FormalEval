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

Example test_hex_key_long : hex_key_spec "753BDCEACDF12345B67C2022EEEFAD890ABCDEF12345BBAA202001111887215E753BD9CEFF23BC337312345B67CEEFABD890ABCDEF12345BBACDF12345B67C2022EEEFAD123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC555547567CEEFAD890ABCDEF12345BBAA20200890AB123ABB333A11DDBCBCDEF20202C0CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF231234567890ABCDEF12345BBAA20200BCCBBD4AA20200CBBD431BDCF0" 186.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.