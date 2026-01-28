Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char
  | "B"%char | "D"%char => true
  | _ => false
  end.

Fixpoint count_prime_hex (s : string) : nat :=
  match s with
  | "" => 0
  | String h t =>
    (if is_prime_hex_digit h then 1 else 0) +
    count_prime_hex t
  end.

Definition hex_key_impl (s : string) : nat :=
  count_prime_hex s.

Definition problem_78_pre (s : string) : Prop := True.

Definition problem_78_spec (s : string) (output : nat) : Prop :=
  output = hex_key_impl s.

Example test_long :
  problem_78_spec
    "753BDC11ABCD2020D45B67C2022EEEFAD890ABCDEF12345BBAA20200CC22EEFFEEDDCCBBAAE0201234567F89ADBCDEF753BDCE02067F89ADBCDEF0"
    50.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold count_prime_hex.
  simpl.
  unfold is_prime_hex_digit.
  (* Due to the length and complexity of the string, we rely on reflexivity after unfolding *)
  reflexivity.
Qed.