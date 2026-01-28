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

Example test_large : problem_78_spec "ACDF11118872159CEFACDF11118872115CE73ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDEFEAD9CEFFCEEFAD213BCCBBD4FCEEFAD1213BCCBBD4" 50.
Proof.
  unfold problem_78_spec.
  unfold hex_key_impl.
  simpl.
  unfold is_prime_hex_digit.
  (* The proof proceeds by repeated unfolding of count_prime_hex and is_prime_hex_digit *)
  (* Manual computation verifies count of prime hex digits is 50 *)
  reflexivity.
Qed.