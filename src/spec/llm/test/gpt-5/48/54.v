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

Example palindrome_long_string_not_palindrome: is_palindrome_spec "areferaWas it a car or a cat I rbWas it aa car ostep on no petsr a ca t I saw?ca" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro Heq.
    simpl in Heq.
    injection Heq as Hhd Htl.
    clear Hhd.
    simpl in Htl.
    discriminate Htl.
Qed.