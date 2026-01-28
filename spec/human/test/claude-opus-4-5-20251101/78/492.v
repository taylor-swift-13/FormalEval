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

Example test_hex_key_long : problem_78_spec "22202273ABB333A11DDBCDBCDEF2BB333A1753BBCCEEEFEADEE11ABCD2020D45B67C2022EEEFAD890ABC7DEF12345BBAA20200CCE22EEFFEEDDCCBBAAEFEADDCEE7753BDCF01DDBC02020CBAABBB2BB333CA11DD2E" 84.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  unfold count_prime_hex.
  unfold is_prime_hex_digit.
  simpl.
  reflexivity.
Qed.