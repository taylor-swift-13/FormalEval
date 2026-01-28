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
(* Input: strings = ["abc"; "bcd"; "cbd"; "dbc"; "cda"], substring = "bc" *)
(* Output: result = ["abc"; "bcd"; "dbc"] *)

Example test_filter_list : filter_by_substring_spec ["abc"; "bcd"; "cbd"; "dbc"; "cda"] "bc" ["abc"; "bcd"; "dbc"].
Proof.
  unfold filter_by_substring_spec.
  
  (* Process "abc": keep *)
  apply filter_keep.
  { exists "a", "". reflexivity. }
  
  (* Process "bcd": keep *)
  apply filter_keep.
  { exists "", "d". reflexivity. }
  
  (* Process "cbd": skip *)
  apply filter_skip.
  { intros [p [s H]]. 
    destruct p; simpl in H; try discriminate.
    destruct p; simpl in H; try discriminate.
    destruct p; simpl in H; try discriminate.
    destruct p; simpl in H; try discriminate.
  }
  
  (* Process "dbc": keep *)
  apply filter_keep.
  { exists "d", "". reflexivity. }
  
  (* Process "cda": skip *)
  apply filter_skip.
  { intros [p [s H]]. 
    destruct p; simpl in H; try discriminate.
    destruct p; simpl in H; try discriminate.
    destruct p; simpl in H; try discriminate.
    destruct p; simpl in H; try discriminate.
  }
  
  (* Base case *)
  apply filter_nil.
Qed.