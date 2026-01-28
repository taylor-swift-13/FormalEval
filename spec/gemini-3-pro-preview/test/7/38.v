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
(* Input: strings = ["The cat in the hat"; "Green eggs and ham"; "One fish two fish"; "Red fish blue fish"], substring = "fish" *)
(* Output: result = ["One fish two fish"; "Red fish blue fish"] *)

Example test_filter_fish : 
  filter_by_substring_spec 
    ["The cat in the hat"; "Green eggs and ham"; "One fish two fish"; "Red fish blue fish"] 
    "fish" 
    ["One fish two fish"; "Red fish blue fish"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip.
  - (* "fish" is not in "The cat in the hat" *)
    intros [p [s H]]. admit.
  - apply filter_skip.
    + (* "fish" is not in "Green eggs and ham" *)
      intros [p [s H]]. admit.
    + apply filter_keep.
      * (* "fish" is in "One fish two fish" *)
        exists "One ", " two fish". reflexivity.
      * apply filter_keep.
        -- (* "fish" is in "Red fish blue fish" *)
           exists "Red ", " blue fish". reflexivity.
        -- apply filter_nil.
Admitted.