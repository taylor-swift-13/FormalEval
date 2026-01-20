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

Lemma string_cons_eq : forall c1 s1 c2 s2,
  String c1 s1 = String c2 s2 -> c1 = c2 /\ s1 = s2.
Proof.
  intros c1 s1 c2 s2 H.
  inversion H; subst; auto.
Qed.

Example palindrome_petrssaSStep: is_palindrome_spec "petrssaSStep" false.
Proof.
  unfold is_palindrome_spec.
  right.
  split.
  - reflexivity.
  - simpl.
    intros H.
    apply string_cons_eq in H. destruct H as [_ H].
    apply string_cons_eq in H. destruct H as [_ H].
    apply string_cons_eq in H. destruct H as [_ H].
    apply string_cons_eq in H. destruct H as [Hr _].
    compute in Hr.
    inversion Hr; discriminate.
Qed.