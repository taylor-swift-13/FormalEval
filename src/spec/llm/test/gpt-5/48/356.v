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

Example palindrome_test_case: is_palindrome_spec "on12zZ2@@@@!3j Z d3!@@@2Zz21" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - unfold not; intro H.
    simpl in H.
    discriminate H.
Qed.