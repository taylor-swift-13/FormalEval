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

Example test_275322022EBDCEEFFBA7537F89ABCDEF002E : problem_78_spec "275322022EBDCEEFFBA7537F89ABCDEF002E" 18.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* "2" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "7" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "5" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "3" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "2" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "2" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "0" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "2" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "2" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "E" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "B" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "D" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "C" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "E" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "E" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "F" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "F" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "B" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "A" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "7" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "5" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "3" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "7" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "F" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "8" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "9" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "A" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "B" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "C" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "D" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "E" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "F" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "0" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "0" not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "2" prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* next "E" not prime *)
  simpl.
  reflexivity.
Qed.