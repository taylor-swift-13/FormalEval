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

Example test_275322022EBDCEEFFA7F89ABCDEF002E : problem_78_spec "275322022EBDCEEFFA7F89ABCDEF002E" 14.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  (* "2" is prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "7" is prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "5" is prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "3" is prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "2" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "2" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "0" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "2" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "2" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "E" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "B" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "D" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "C" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "E" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "E" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "F" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "F" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "A" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "7" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "F" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "8" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "9" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "A" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "B" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "C" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "D" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "E" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "F" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "0" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "0" not prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "2" prime *)
  simpl.
  unfold is_prime_hex_digit.
  (* "E" not prime *)
  simpl.
  reflexivity.
Qed.