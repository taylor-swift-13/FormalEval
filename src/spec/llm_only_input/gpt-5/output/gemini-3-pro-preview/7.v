Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Require Import Lia.

Definition contains_substring (s sub : string) : Prop :=
  exists prefix suffix, s = prefix ++ sub ++ suffix.

Inductive FilterRel (sub : string) : list string -> list string -> Prop :=
| filter_nil : FilterRel sub [] []
| filter_keep : forall s l l',
    contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) (s :: l')
| filter_skip : forall s l l',
    ~ contains_substring s sub ->
    FilterRel sub l l' ->
    FilterRel sub (s :: l) l'.

Definition filter_by_substring_spec (strings : list string) (substring : string) (result : list string) : Prop :=
  FilterRel substring strings result.

Lemma length_append : forall s1 s2,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1 as [|a s1 IH]; intros s2; simpl.
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma contains_substring_length_le : forall s sub,
  contains_substring s sub -> String.length sub <= String.length s.
Proof.
  intros s sub [prefix [suffix Heq]].
  rewrite Heq.
  repeat rewrite length_append.
  lia.
Qed.

Example test_case_filter_by_substring_empty_output :
  filter_by_substring_spec [""; "john"] "johnx" [].
Proof.
  unfold filter_by_substring_spec.
  eapply filter_skip.
  - unfold not; intros H.
    apply contains_substring_length_le in H.
    simpl in H. lia.
  - eapply filter_skip.
    + unfold not; intros H.
      apply contains_substring_length_le in H.
      simpl in H. lia.
    + apply filter_nil.
Qed.