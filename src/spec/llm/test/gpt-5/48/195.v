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

Definition is_dot (a : ascii) : bool :=
  if Ascii.ascii_dec a "." then true else false.

Definition starts_with_dot (s : string) : bool :=
  match s with
  | EmptyString => false
  | String a _ => is_dot a
  end.

Example palindrome_non_pal: is_palindrome_spec " Able wliveas I ere I saw Elba." false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    apply (f_equal starts_with_dot) in H.
    simpl in H.
    discriminate H.
Qed.