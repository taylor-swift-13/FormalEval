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

Example palindrome_a_man_a_plan_geesea_canal_panama: is_palindrome_spec "A man, a plan, geesea canal: Panama" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. unfold not. intro H. injection H as Hhd Htl. compute in Hhd. congruence.
Qed.