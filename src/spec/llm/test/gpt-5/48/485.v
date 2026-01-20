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

Example palindrome_complex_string_false: is_palindrome_spec "erecainA man, a plan, a erecaisnral,  Pa12zZ2@@@@!@3Taco notj  d3!@@@2Z.z21nama.WAsnral,Dd3!@@@2DoZz21o" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. intro H. discriminate.
Qed.