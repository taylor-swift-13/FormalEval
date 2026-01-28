Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* Specification definitions *)
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

(* Helper lemmas to reason about string length *)
Lemma string_length_append : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  intros s1 s2. induction s1; simpl; auto.
  rewrite IHs1. reflexivity.
Qed.

Lemma contains_substring_bound : forall s sub, contains_substring s sub -> String.length sub <= String.length s.
Proof.
  intros s sub [pre [suf H]].
  rewrite H.
  repeat rewrite string_length_append.
  rewrite Nat.add_assoc.
  apply Nat.le_trans with (m := String.length pre + String.length sub).
  - apply Nat.le_add_l.
  - apply Nat.le_add_r.
Qed.

Lemma not_contains_if_shorter : forall s sub, String.length s < String.length sub -> ~ contains_substring s sub.
Proof.
  intros s sub Hlen Hcont.
  apply contains_substring_bound in Hcont.
  apply Nat.lt_nge in Hlen.
  contradiction.
Qed.

(* Test case verification *)
(* Input: strings = ["hello"; "world"; "python"; "numpy"; "pandas"], substring = "antidisestablishmentariasaturnnismpy" *)
(* Output: result = [] *)

Example test_filter_long : filter_by_substring_spec ["hello"; "world"; "python"; "numpy"; "pandas"] "antidisestablishmentariasaturnnismpy" [].
Proof.
  unfold filter_by_substring_spec.
  repeat apply filter_skip.
  all: try apply filter_nil.
  all: apply not_contains_if_shorter; simpl; repeat constructor.
Qed.