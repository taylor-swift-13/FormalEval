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

Example palindrome_long_string: is_palindrome_spec "abaWas ait a car or a sacat I saw?bbcc" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl. destruct (String.string_dec "abaWas ait a car or a sacat I saw?bbcc" "ccbb?was I tacas a ro rac a tia saWaba") as [Heq|Hneq].
    + discriminate Heq.
    + exact Hneq.
Qed.