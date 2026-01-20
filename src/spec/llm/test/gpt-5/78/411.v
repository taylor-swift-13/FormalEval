Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Local Open Scope string_scope.
Local Open Scope Z_scope.

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

Example hex_key_long_nat: hex_key_spec "7ABCDEF20202011ACD2020DDBB123ACDF12345B67C2022EEEFAD890AB123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF23BCCBBD4DEF12345BBBBAACB275322022EBDCABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC5ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55555557F89ABCDEF002EAABBBBB33773A11DDBC535553BD" 186.
Proof.
  unfold hex_key_spec.
  vm_compute.
  reflexivity.
Qed.

Example hex_key_long_Z: Z.of_nat (count_prime_hex "7ABCDEF20202011ACD2020DDBB123ACDF12345B67C2022EEEFAD890AB123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF23BCCBBD4DEF12345BBBBAACB275322022EBDCABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC5ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55555557F89ABCDEF002EAABBBBB33773A11DDBC535553BD") = 186%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.