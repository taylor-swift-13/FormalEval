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

Example palindrome_test_case: is_palindrome_spec "foeIemwsaStep12zZ2petssaw@@@@!3j  12zZ2@@@@!Able was I ere I saw Elba.j3jd3!@@@2Zz21AeNA,noan," false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    compute in H.
    injection H as Hh Ht.
    clear Ht.
    inversion Hh.
Qed.