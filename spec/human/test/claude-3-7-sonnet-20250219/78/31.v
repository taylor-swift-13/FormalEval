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

Example test_77C67ABCD237777 : problem_78_spec "77C67ABCD237777" 11.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'C' not prime -> 0 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '6' not prime -> 0 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'A' not prime -> 0 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'B' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'C' not prime -> 0 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* 'D' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '2' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '3' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime -> 1 + ... *)
  unfold is_prime_hex_digit.
  simpl.
  (* '7' prime -> 1 + ... *)
  simpl.
  reflexivity.
Qed.