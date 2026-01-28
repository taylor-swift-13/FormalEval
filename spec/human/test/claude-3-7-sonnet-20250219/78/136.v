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

Example test_ABDBC5555 : problem_78_spec "ABDBC5555" 7.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* Counting occurrences: A(0) + B(1) + D(1) + B(1) + C(0) + 5(1) + 5(1) + 5(1) + 5(1) = 7 *)
  reflexivity.
Qed.