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

Example test_hex_key_long : problem_78_spec "AB11DDBC5555753BD1234571234567BB333A11DDBC53BD7890ABCDEF12345BBAA2753BDCE02067F89ADBCDEF00EF12345BBAA20200" 59.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  reflexivity.
Qed.