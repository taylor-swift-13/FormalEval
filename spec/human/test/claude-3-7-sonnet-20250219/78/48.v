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

Example test_67ABCD2 : problem_78_spec "67ABCD2" 4.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  (* '6' is not prime digit, 0 *)
  simpl.
  unfold is_prime_hex_digit.
  (* '7' is prime digit, 1 *)
  simpl.
  unfold is_prime_hex_digit.
  (* 'A' not prime digit, 0 *)
  simpl.
  unfold is_prime_hex_digit.
  (* 'B' prime digit, 1 *)
  simpl.
  unfold is_prime_hex_digit.
  (* 'C' not prime digit, 0 *)
  simpl.
  unfold is_prime_hex_digit.
  (* 'D' prime digit, 1 *)
  simpl.
  unfold is_prime_hex_digit.
  (* '2' prime digit, 1 *)
  simpl.
  reflexivity.
Qed.