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

Example test_complex : problem_78_spec "1234567CEEFAD890ABCD73ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55550" 39.
Proof.
  unfold problem_78_spec, hex_key_impl.
  simpl.
  (* unfold is_prime_hex_digit and evaluate count through the string *)
  (* The tactic below automates the evaluation for this specific string input *)
  (* We proceed by simplification and repeatedly evaluating is_prime_hex_digit on each character *)
  (* Because is_prime_hex_digit is a simple match, simpl can reduce most of it *)
  (* We use repeat simpl to fully reduce the count *)
  repeat (
    match goal with
    | |- context[String ?c ?t] =>
      simpl;
      unfold is_prime_hex_digit;
      simpl
    end).
  reflexivity.
Qed.