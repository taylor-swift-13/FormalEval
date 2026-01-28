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

Example test_776B7AB1111189448898989CBD22377 : problem_78_spec "776B7AB1111189448898989CBD22377" 12.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.

  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '6' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'B' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'A' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'B' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '1' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '1' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '1' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '1' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '8' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '9' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '4' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '4' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '8' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '8' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '9' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '8' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '9' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'C' not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'B' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'D' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '2' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '2' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '3' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime *)
  simpl.

  reflexivity.
Qed.