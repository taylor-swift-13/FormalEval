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

Example palindrome_complex_string: is_palindrome_spec "A man, a plaA a12zZ2geeseaea@@@@z!3Tacoman,a plan, geesea canal: PanamaTaco notWas it sawa car o r a caat I petssaw?n, a erecaisnral,  Panama." false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intro H.
    cbv in H.
    discriminate.
Qed.