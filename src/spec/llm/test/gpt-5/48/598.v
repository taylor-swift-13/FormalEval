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

Example palindrome_complex_string: is_palindrome_spec "cEcvilcd3!@@@2 ord3!a@@@2Zz21oeman,Able wliveas I ere I saw Elba.name1" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    simpl in H.
    discriminate.
Qed.