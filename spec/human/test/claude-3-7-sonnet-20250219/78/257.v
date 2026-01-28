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

Example test_complex : problem_78_spec
  "73ABB3033A11DFAD753BDDBCBCDEF202020CBAABBB2BB333CA11D0DBC5555" 38.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold count_prime_hex.
  simpl.

  (* Counting each character in order: *)
  (* '7' is prime digit -> 1 *)
  (* '3' is prime digit -> 1 *)
  (* 'A' not prime -> 0 *)
  (* 'B' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* '3' prime -> 1 *)
  (* '0' not prime -> 0 *)
  (* '3' prime -> 1 *)
  (* '3' prime -> 1 *)
  (* 'A' not prime -> 0 *)
  (* '1' not prime -> 0 *)
  (* '1' not prime -> 0 *)
  (* 'D' prime -> 1 *)
  (* 'F' not prime -> 0 *)
  (* 'A' not prime -> 0 *)
  (* 'D' prime -> 1 *)
  (* '7' prime -> 1 *)
  (* '5' prime -> 1 *)
  (* '3' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* 'D' prime -> 1 *)
  (* 'D' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* 'C' not prime -> 0 *)
  (* 'B' prime -> 1 *)
  (* 'C' not prime -> 0 *)
  (* 'D' prime -> 1 *)
  (* 'E' not prime -> 0 *)
  (* 'F' not prime -> 0 *)
  (* '2' prime -> 1 *)
  (* '0' not prime -> 0 *)
  (* '2' prime -> 1 *)
  (* '0' not prime -> 0 *)
  (* '2' prime -> 1 *)
  (* '0' not prime -> 0 *)
  (* 'C' not prime -> 0 *)
  (* 'B' prime -> 1 *)
  (* 'A' not prime -> 0 *)
  (* 'A' not prime -> 0 *)
  (* 'B' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* '2' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* '3' prime -> 1 *)
  (* '3' prime -> 1 *)
  (* '3' prime -> 1 *)
  (* 'C' not prime -> 0 *)
  (* 'A' not prime -> 0 *)
  (* '1' not prime -> 0 *)
  (* '1' not prime -> 0 *)
  (* 'D' prime -> 1 *)
  (* '0' not prime -> 0 *)
  (* 'D' prime -> 1 *)
  (* 'B' prime -> 1 *)
  (* 'C' not prime -> 0 *)
  (* '5' prime -> 1 *)
  (* '5' prime -> 1 *)
  (* '5' prime -> 1 *)
  (* '5' prime -> 1 *)
  simpl.
  reflexivity.
Qed.