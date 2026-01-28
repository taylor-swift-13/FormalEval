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

Example test_ACDF11118872159CEFFCEEFAD213BCCBBBD4 : problem_78_spec "ACDF11118872159CEFFCEEFAD213BCCBBBD4" 12.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  simpl.
  (* A is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* C is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* D is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* F is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 1 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 1 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 1 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 1 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 8 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 8 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 7 is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 2 is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 1 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 5 is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 9 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* C is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* E is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* F is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* F is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* C is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* E is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* E is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* F is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* A is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* D is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 2 is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 1 is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 3 is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* B is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* C is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* C is not prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* B is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* B is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* B is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* D is prime *)
  unfold is_prime_hex_digit.
  simpl.
  (* 4 is not prime *)
  reflexivity.
Qed.