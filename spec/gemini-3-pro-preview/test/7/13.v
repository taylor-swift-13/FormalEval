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
(* Input: strings = [["moon"; "stars"; "sun"; "planets"]; "s"], output = ["stars"; "sun"; "planets"] *)

Example test_filter_complex : filter_by_substring_spec ["moon"; "stars"; "sun"; "planets"] "s" ["stars"; "sun"; "planets"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip.
  - intros [pre [suf H]].
    destruct pre; simpl in H; [discriminate|].
    injection H as _ H.
    destruct pre; simpl in H; [discriminate|].
    injection H as _ H.
    destruct pre; simpl in H; [discriminate|].
    injection H as _ H.
    destruct pre; simpl in H; [discriminate|].
    injection H as _ H.
    destruct pre; simpl in H; discriminate.
  - apply filter_keep.
    + exists "", "tars". simpl. reflexivity.
    + apply filter_keep.
      * exists "", "un". simpl. reflexivity.
      * apply filter_keep.
        { exists "planet", "". simpl. reflexivity. }
        { apply filter_nil. }
Qed.