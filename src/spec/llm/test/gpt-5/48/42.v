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

Example palindrome_never_odd_or_e_ven: is_palindrome_spec "never odd or e ven" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    pose proof (string_dec "never odd or e ven" "nev e ro ddo reven") as Hdec.
    simpl in Hdec.
    destruct Hdec as [Heq | Hneq].
    + rewrite Heq. congruence.
    + exact Hneq.
Qed.