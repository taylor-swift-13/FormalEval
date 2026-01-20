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

Definition head_char (s : string) : ascii :=
  match s with
  | EmptyString => Ascii.Ascii false false false false false false false false
  | String a _ => a
  end.

Example palindrome_was_it_a_car_or_a_cat_i_saw: is_palindrome_spec "Was it a car or a cat I saw?" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    intro H.
    pose proof (f_equal head_char H) as Hh.
    simpl in Hh.
    apply (f_equal Ascii.nat_of_ascii) in Hh.
    simpl in Hh.
    discriminate.
Qed.