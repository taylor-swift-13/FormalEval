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

Example palindrome_complex_string: is_palindrome_spec "a12zZ2geStepElba.eTaco cEvil is a name 1WeenWPanama..A man, a plan, a erStep osawn no petsecaisnral,  Panam a.sLmxahinksf a foeman, as IcananWA live.atn,a" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. unfold not. intro H. congruence.
Qed.