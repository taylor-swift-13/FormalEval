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

Example palindrome_complex_string: is_palindrome_spec "A maPa canal, Pana,mano canal12zZ2@@Aorcatgees,Panamae@@!2j3jd3!@@@2Zz21, Pana.ma." false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    simpl in H.
    discriminate H.
Qed.