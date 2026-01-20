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

Example palindrome_f12zZ2_man_A: is_palindrome_spec "f12zZ2@@@man,A" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. intros H. discriminate.
Qed.