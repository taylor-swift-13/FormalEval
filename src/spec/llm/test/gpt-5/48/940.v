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

Example palindrome_new_test: is_palindrome_spec "A man, a pnl,an, a canal: ,Step1etssaw@@@@!3j  12zZ2@@@@!Able was I ere I saw Elba.j3jd3!@@@2Zz21aPanama" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    simpl in H.
    injection H as Hhd Htl.
    compute in Hhd.
    congruence.
Qed.