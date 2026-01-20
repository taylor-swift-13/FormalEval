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

Example palindrome_long_false: is_palindrome_spec "12zZ2@@j@@!j312zZas2@@j@@!j3jd3!@@@2Zz21jd3!@z@@2Zz2lieveA" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    compute in H.
    inversion H.
Qed.