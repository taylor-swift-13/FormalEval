Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint count_prime_hex_digits (chars : list ascii) : nat :=
  match chars with
  | [] => 0
  | c :: rest => (if is_prime_hex_digit c then 1 else 0) + count_prime_hex_digits rest
  end.

Definition hex_key_spec (num : string) (result : nat) : Prop :=
  result = count_prime_hex_digits (string_to_list num).

Example test_hex_key : hex_key_spec "AC377ABCDEF20ABCDEF202020CBAABBBBB333A11DDBC555520222E2020CBAABBBBB333A11DDBCEE11ABCD2020D45B67C2022EEEFAD890ABCDEF12345BBAA20200CC22EEFFEEDDCCBBAAEFEADC55553BD53DF12345B767C2022EEEFAD890AB123ABB333A11DDBCBCDEF2020C20CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF231234567890ABCDEF12345BBAA20200BCCBBD4" 163.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.