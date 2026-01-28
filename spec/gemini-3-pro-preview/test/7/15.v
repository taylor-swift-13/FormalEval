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
(* Input: strings = ["hello"; "world"; "python"; "numpy"; "pandas"; "numpy"], substring = "py" *)
(* Output: result = ["python"; "numpy"; "numpy"] *)

Example test_filter_py : filter_by_substring_spec ["hello"; "world"; "python"; "numpy"; "pandas"; "numpy"] "py" ["python"; "numpy"; "numpy"].
Proof.
  unfold filter_by_substring_spec.
  
  (* "hello" does not contain "py" *)
  apply filter_skip.
  { intros [p [s H]]. do 10 (destruct p; simpl in H; try discriminate). }
  
  (* "world" does not contain "py" *)
  apply filter_skip.
  { intros [p [s H]]. do 10 (destruct p; simpl in H; try discriminate). }
  
  (* "python" contains "py" *)
  apply filter_keep.
  { exists "", "thon". reflexivity. }
  
  (* "numpy" contains "py" *)
  apply filter_keep.
  { exists "num", "". reflexivity. }
  
  (* "pandas" does not contain "py" *)
  apply filter_skip.
  { intros [p [s H]]. do 10 (destruct p; simpl in H; try discriminate). }
  
  (* "numpy" contains "py" *)
  apply filter_keep.
  { exists "num", "". reflexivity. }
  
  (* Base case *)
  apply filter_nil.
Qed.