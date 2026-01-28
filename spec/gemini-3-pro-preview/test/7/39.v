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
(* Input: strings = ["The Shawshank Redemption"; "The Godfather"; "The Dark Knight"; "The Lord of the Rings"; "Star Wars"; "Inception"; "Forrest Gump"], substring = "he" *)
(* Output: result = ["The Shawshank Redemption"; "The Godfather"; "The Dark Knight"; "The Lord of the Rings"] *)

Example test_filter_movies : 
  filter_by_substring_spec 
    ["The Shawshank Redemption"; "The Godfather"; "The Dark Knight"; "The Lord of the Rings"; "Star Wars"; "Inception"; "Forrest Gump"] 
    "he" 
    ["The Shawshank Redemption"; "The Godfather"; "The Dark Knight"; "The Lord of the Rings"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  { exists "T", " Shawshank Redemption". reflexivity. }
  apply filter_keep.
  { exists "T", " Godfather". reflexivity. }
  apply filter_keep.
  { exists "T", " Dark Knight". reflexivity. }
  apply filter_keep.
  { exists "T", " Lord of the Rings". reflexivity. }
  apply filter_skip.
  { intros [p [q H]]. do 20 (destruct p; simpl in H; try discriminate). }
  apply filter_skip.
  { intros [p [q H]]. do 20 (destruct p; simpl in H; try discriminate). }
  apply filter_skip.
  { intros [p [q H]]. do 20 (destruct p; simpl in H; try discriminate). }
  apply filter_nil.
Qed.