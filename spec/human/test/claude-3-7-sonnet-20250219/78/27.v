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

Example test_1679D99999ABCD23 : problem_78_spec "1679D99999ABCD23" 6.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '1' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '6' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '7' -> true *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '9' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* 'D' -> true *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '9' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '9' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '9' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '9' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* 'A' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* 'B' -> true *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* 'C' -> false *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* 'D' -> true *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '2' -> true *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '3' -> true *)
  simpl.
  reflexivity.
Qed.