Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String a s' => String.append (rev_string s') (String a EmptyString)
  end.

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  (result = true /\ text = rev_string text) \/
  (result = false /\ text <> rev_string text).

Example palindrome_carriage_return: is_palindrome_spec (String (Ascii.ascii_of_nat 13) EmptyString) true.
Proof.
  unfold is_palindrome_spec.
  left.
  split.
  - reflexivity.
  - simpl. reflexivity.
Qed.