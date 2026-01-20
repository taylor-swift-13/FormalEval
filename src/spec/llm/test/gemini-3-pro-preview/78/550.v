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

Example test_hex_key : hex_key_spec "275322022EBDCABB333A11DDBCBC753BDC11ABCD2020D45B67C2022EEEFAD890ABCDEF1234275322022EBDCEEFFBA7F345BBAA2020015E753BD9CEFF23BCCBBD4C2022EEEFAD890AB2753BDCEEFAD20201234567F89ABCDEF02202CEFEA2D22ECDEF122345BBAA202003EF0DEF202020CBAABBB2BB333CA11DDBC5ABB333A11DDBCBCDEF2202020CBAABBB2BB333CA11DDBC55555557F89ABCDEF002E" 163.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.