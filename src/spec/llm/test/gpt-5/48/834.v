Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Local Open Scope string_scope.

Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String a s' => String.append (rev_string s') (String a EmptyString)
  end.

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  (result = true /\ text = rev_string text) \/
  (result = false /\ text <> rev_string text).

Example palindrome_fIoem_an_I: is_palindrome_spec "fIoem,an,I" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - intros H.
    assert (Hrev: rev_string "fIoem,an,I" = "I,na,meoIf") by reflexivity.
    rewrite Hrev in H.
    discriminate.
Qed.