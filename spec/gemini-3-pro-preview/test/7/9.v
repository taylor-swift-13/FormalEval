Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
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

(* Test case verification *)
(* Input: strings = ["a"; "ab"; "abc"; "abcd"; "abcde"; "bcde"; "cde"], substring = "cd" *)
(* Output: result = ["abcd"; "abcde"; "bcde"; "cde"] *)

Example test_filter_complex : filter_by_substring_spec ["a"; "ab"; "abc"; "abcd"; "abcde"; "bcde"; "cde"] "cd" ["abcd"; "abcde"; "bcde"; "cde"].
Proof.
  unfold filter_by_substring_spec.
  (* "a" *)
  apply filter_skip.
  { unfold contains_substring. intros [p [q H]].
    destruct p; simpl in H; [discriminate|].
    injection H as _ H. destruct p; simpl in H; discriminate. }
  (* "ab" *)
  apply filter_skip.
  { unfold contains_substring. intros [p [q H]].
    destruct p; simpl in H; [discriminate|].
    injection H as _ H. destruct p; simpl in H; [discriminate|].
    injection H as _ H. destruct p; simpl in H; discriminate. }
  (* "abc" *)
  apply filter_skip.
  { unfold contains_substring. intros [p [q H]].
    destruct p; simpl in H; [discriminate|].
    injection H as _ H. destruct p; simpl in H; [discriminate|].
    injection H as _ H. destruct p; simpl in H; [discriminate|].
    injection H as _ H. destruct p; simpl in H; discriminate. }
  (* "abcd" *)
  apply filter_keep.
  { exists "ab", "". reflexivity. }
  (* "abcde" *)
  apply filter_keep.
  { exists "ab", "e". reflexivity. }
  (* "bcde" *)
  apply filter_keep.
  { exists "b", "e". reflexivity. }
  (* "cde" *)
  apply filter_keep.
  { exists "", "e". reflexivity. }
  (* [] *)
  apply filter_nil.
Qed.