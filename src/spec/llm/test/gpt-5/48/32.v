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

Example palindrome_test: is_palindrome_spec "aaWas it a car or a cat I rbWas it a car ostep on no petsr a ca t I saw?ca" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    apply (f_equal (fun s =>
      match s with
      | EmptyString => None
      | String _ EmptyString => None
      | String _ (String b _) => Some b
      end)) in H.
    simpl in H.
    discriminate.
Qed.