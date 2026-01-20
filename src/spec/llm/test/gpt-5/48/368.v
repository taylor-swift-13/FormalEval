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

Example palindrome_SSSoo_notS: is_palindrome_spec "SSSoo notS" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intros H.
    simpl in H.
    apply (f_equal (fun s => match s with
                             | EmptyString => EmptyString
                             | String a s' => s'
                             end)) in H.
    simpl in H.
    apply (f_equal (fun s => match s with
                             | EmptyString => Ascii.Ascii false false false false false false false false
                             | String a s' => a
                             end)) in H.
    simpl in H.
    discriminate.
Qed.