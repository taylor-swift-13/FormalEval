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

Example test_hex_key : hex_key_spec "123ABB333A11DDBCBCDEF202020CBAABBB73533A11DDBC555547567CEEFAD890ABCDEF12345BBAA2020123F4567CEEFA7ABCDEF20ABCDEF202020CBAABBBBB333A11DDBC555520222E2020CBAABBBBB333A11DDBCACDF111188727159CEFFCEEFAD12113BCCBBD4EE11ACDF11118872159CEFFCEEFAD21753BDCEE753BDCF03BCCBBBD4ABCD2020D45B67C2022EEEFAD890ABCDEF12345BBAA20200CC22EEFFEEDDCCBBAAEFEADC55553BACDF11118872159CEEFFCEEFAD213BCCBBD4DD89073533ABCDEF12345BBBAA20200" 187.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.