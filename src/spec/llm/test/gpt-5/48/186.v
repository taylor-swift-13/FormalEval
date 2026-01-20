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

Example palindrome_complex_string_false: is_palindrome_spec "nWA man, a pmlan, a erecaisnral,  Panama.sLmxhink" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    pose proof (f_equal (fun s => match s with | EmptyString => 0%nat | String a _ => nat_of_ascii a end) H) as H0.
    simpl in H0.
    discriminate H0.
Qed.