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

Example palindrome_lEvil_false: is_palindrome_spec "lEvil" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    simpl in H.
    apply (f_equal (fun s => match s with
                             | String _ s' => s'
                             | EmptyString => EmptyString
                             end)) in H.
    simpl in H.
    apply (f_equal (fun s => match s with
                             | String a _ => a
                             | EmptyString => Ascii.Ascii false false false false false false false false
                             end)) in H.
    simpl in H.
    discriminate.
Qed.