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

Example palindrome_complex_string: is_palindrome_spec "d3!@@@2 Able wliveas I ere I saw Elba.name1" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    set (head := fun s : string => match s with | EmptyString => "a"%char | String c _ => c end).
    apply (f_equal head) in H.
    unfold head in H.
    clear head.
    compute in H.
    apply (f_equal Ascii.nat_of_ascii) in H.
    compute in H.
    discriminate.
Qed.