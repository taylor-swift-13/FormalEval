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

Example palindrome_test_case: is_palindrome_spec "a12zZ2g@eeseaea@@@@!31Tacoman," false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - destruct (string_dec "a12zZ2g@eeseaea@@@@!31Tacoman," (rev_string "a12zZ2g@eeseaea@@@@!31Tacoman,")) as [Heq | Hne].
    + simpl in Heq. inversion Heq.
    + exact Hne.
Qed.