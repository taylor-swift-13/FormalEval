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

Example palindrome_long_string_false: is_palindrome_spec "12zZ2@@@@!@3Taco notj  d3!@@@2DoZz2112zZ2@@@@!@3Taco notj  d3!@@@2DoZz212Zz21oeman," false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - unfold not; intro H; simpl in H; discriminate.
Qed.