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

Example palindrome_long_string_false: is_palindrome_spec "abbbWas it a car oaaaabcar I rbWas it a car ostep on no petsr a ca t I saw?cat I saw?referc" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    unfold not; intro H.
    injection H as Ha Hs.
    simpl in Ha.
    discriminate Ha.
Qed.