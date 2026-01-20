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
(* Input: strings = ["cat"; "dog"; "elephant"; "rhinoceros"; "seagull"], substring = "e" *)
(* Output: result = ["elephant"; "rhinoceros"; "seagull"] *)

Example test_filter_list : filter_by_substring_spec ["cat"; "dog"; "elephant"; "rhinoceros"; "seagull"] "e" ["elephant"; "rhinoceros"; "seagull"].
Proof.
  unfold filter_by_substring_spec.
  
  (* "cat" does not contain "e" *)
  apply filter_skip.
  { intros [p [s H]].
    repeat (destruct p; simpl in H; [ discriminate | inversion H; subst ]). }
  
  (* "dog" does not contain "e" *)
  apply filter_skip.
  { intros [p [s H]].
    repeat (destruct p; simpl in H; [ discriminate | inversion H; subst ]). }

  (* "elephant" contains "e" *)
  apply filter_keep.
  { exists "", "lephant". reflexivity. }

  (* "rhinoceros" contains "e" *)
  apply filter_keep.
  { exists "rhinoc", "ros". reflexivity. }

  (* "seagull" contains "e" *)
  apply filter_keep.
  { exists "s", "agull". reflexivity. }

  (* Base case *)
  apply filter_nil.
Qed.