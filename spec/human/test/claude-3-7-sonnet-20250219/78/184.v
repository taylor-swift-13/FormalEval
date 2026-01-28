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

Example test_202222E : problem_78_spec "202222E" 5.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "2" is prime hex digit, so 1 + count of "02222E" *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "0" not prime, 0 + count of "2222E" *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "2" prime, 1 + count of "222E" *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "2" prime, 1 + count of "22E" *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "2" prime, 1 + count of "2E" *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "2" prime, 1 + count of "E" *)
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "E" not prime, 0 + count of "" *)
  simpl.
  (* count "" = 0, so total is 1 + 0 + 1 + 1 + 1 + 1 + 0 = 5 *)
  reflexivity.
Qed.