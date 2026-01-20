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

Example palindrome_long_string: is_palindrome_spec "Panama.d3!@@@2Zzeman,ma.PanamalnotsLmxhink," false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - unfold not.
    intro Heq.
    cbv in Heq.
    inversion Heq; discriminate.
Qed.