Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

Lemma correctly_bracketed_starts_with_open : forall s,
  is_correctly_bracketed s -> s <> "" ->
  exists c rest, s = String c rest /\ c = "<"%char.
Proof.
  intros s H Hne.
  induction H.
  - contradiction.
  - exists "<"%char. exists (l ++ ">"). split; reflexivity.
  - destruct (string_dec l1 "").
    + subst. simpl in *. apply IHis_correctly_bracketed2. assumption.
    + destruct (IHis_correctly_bracketed1 n) as [c [rest [Heq Hc]]].
      exists c. exists (rest ++ l2). subst. split; reflexivity.
Qed.

Lemma single_close_not_bracketed : ~ is_correctly_bracketed ">".
Proof.
  intro H.
  assert (Hne: ">" <> "") by discriminate.
  destruct (correctly_bracketed_starts_with_open ">" H Hne) as [c [rest [Heq Hc]]].
  inversion Heq.
  subst.
  discriminate.
Qed.

Example test_problem_56 : problem_56_spec ">" false.
Proof.
  unfold problem_56_spec.
  split.
  - intros H. discriminate.
  - intros H. exfalso. apply single_close_not_bracketed. exact H.
Qed.