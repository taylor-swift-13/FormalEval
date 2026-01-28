Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.

Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String a s' => String.append (rev_string s') (String a EmptyString)
  end.

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  (result = true /\ text = rev_string text) \/
  (result = false /\ text <> rev_string text).

Example test_palindrome_complex : is_palindrome_spec "A man,Taco cEvil i12zZ2@@@@!@3Tacos a name of a foeman, as I live.at a plannWA man, a pmlan, a erecaisnral,  Panama.sLmxhink, geesea canal: Panama" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. intro H. discriminate.
Qed.