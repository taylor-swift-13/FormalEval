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

Example palindrome_test_case: is_palindrome_spec "reWas it a car or a cat I saw?fer" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    intro H.
    apply (f_equal (fun s => match s with | EmptyString => EmptyString | String _ s' => s' end)) in H.
    apply (f_equal (fun s => match s with | EmptyString => EmptyString | String _ s' => s' end)) in H.
    discriminate H.
Qed.