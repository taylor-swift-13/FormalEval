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

Lemma string_head_char_neq: forall a b s t, a <> b -> String a s <> String b t.
Proof.
  intros a b s t Hneq Heq.
  inversion Heq.
  apply Hneq.
  assumption.
Qed.

Example palindrome_see: is_palindrome_spec "see" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    assert (Hne : "s"%char <> "e"%char).
    { destruct (Ascii.ascii_dec "s"%char "e"%char) as [Heq|Hneq].
      - inversion Heq.
      - exact Hneq.
    }
    eapply string_head_char_neq.
    exact Hne.
Qed.