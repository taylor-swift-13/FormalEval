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

Example palindrome_tacot_cat: is_palindrome_spec "Tacot cat" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    pose proof (string_dec "Tacot cat" "tac tocaT") as Hdec.
    destruct Hdec as [Heq|Hneq].
    + exfalso. discriminate Heq.
    + exact Hneq.
Qed.