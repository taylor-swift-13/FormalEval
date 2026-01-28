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
(* Input: strings = ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"], substring = "an" *)
(* Output: result = ["San Francisco"] *)

Example test_filter_cities : 
  filter_by_substring_spec 
    ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"] 
    "an" 
    ["San Francisco"].
Proof.
  unfold filter_by_substring_spec.
  (* Washington *)
  apply filter_skip.
  { intros [p [suf H]].
    do 25 (destruct p as [|? p]; simpl in H; 
      [ repeat (simpl in H; try discriminate; injection H as Hc H; try discriminate Hc) 
      | try discriminate; injection H as _ H ]). }
  (* DC *)
  apply filter_skip.
  { intros [p [suf H]].
    do 25 (destruct p as [|? p]; simpl in H; 
      [ repeat (simpl in H; try discriminate; injection H as Hc H; try discriminate Hc) 
      | try discriminate; injection H as _ H ]). }
  (* New York City *)
  apply filter_skip.
  { intros [p [suf H]].
    do 25 (destruct p as [|? p]; simpl in H; 
      [ repeat (simpl in H; try discriminate; injection H as Hc H; try discriminate Hc) 
      | try discriminate; injection H as _ H ]). }
  (* Boston *)
  apply filter_skip.
  { intros [p [suf H]].
    do 25 (destruct p as [|? p]; simpl in H; 
      [ repeat (simpl in H; try discriminate; injection H as Hc H; try discriminate Hc) 
      | try discriminate; injection H as _ H ]). }
  (* Los Angeles *)
  apply filter_skip.
  { intros [p [suf H]].
    do 25 (destruct p as [|? p]; simpl in H; 
      [ repeat (simpl in H; try discriminate; injection H as Hc H; try discriminate Hc) 
      | try discriminate; injection H as _ H ]). }
  (* San Francisco *)
  apply filter_keep.
  { exists "S", " Francisco". reflexivity. }
  (* Miami *)
  apply filter_skip.
  { intros [p [suf H]].
    do 25 (destruct p as [|? p]; simpl in H; 
      [ repeat (simpl in H; try discriminate; injection H as Hc H; try discriminate Hc) 
      | try discriminate; injection H as _ H ]). }
  (* End *)
  apply filter_nil.
Qed.