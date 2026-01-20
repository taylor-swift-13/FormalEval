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

Example palindrome_Taco_catgeese: is_palindrome_spec "Taco catgeese" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro Heq.
    apply (f_equal (fun s => match s with
                             | EmptyString => 0
                             | String a _ => Ascii.nat_of_ascii a
                             end)) in Heq.
    compute in Heq.
    discriminate Heq.
Qed.