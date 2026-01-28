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

Example test_AB : problem_78_spec "AB" 1.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  (* Evaluate is_prime_hex_digit "A": *)
  unfold is_prime_hex_digit.
  (* "A" is not one of the prime digits, so the first digit count is 0 *)
  simpl.
  (* Now considering the tail "B": *)
  simpl.
  unfold is_prime_hex_digit.
  (* "B" matches prime digit, so count is 1 *)
  simpl.
  (* Sum 0 + 1 = 1 *)
  reflexivity.
Qed.