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
(* Input: strings = ["xxx"; "asd"; "xxy"; "john doe"; "xxxAAA"; "xxx"], substring = "xxx" *)
(* Output: result = ["xxx"; "xxxAAA"; "xxx"] *)

Example test_filter_complex : 
  filter_by_substring_spec ["xxx"; "asd"; "xxy"; "john doe"; "xxxAAA"; "xxx"] "xxx" ["xxx"; "xxxAAA"; "xxx"].
Proof.
  unfold filter_by_substring_spec.
  
  (* 1. "xxx" - keep *)
  apply filter_keep.
  { exists "", "". reflexivity. }
  
  (* 2. "asd" - skip *)
  apply filter_skip.
  { 
    unfold contains_substring. intros [p [s H]].
    repeat (destruct p as [|? p]; simpl in H; try discriminate).
  }

  (* 3. "xxy" - skip *)
  apply filter_skip.
  { 
    unfold contains_substring. intros [p [s H]].
    repeat (destruct p as [|? p]; simpl in H; try discriminate).
  }

  (* 4. "john doe" - skip *)
  apply filter_skip.
  { 
    unfold contains_substring. intros [p [s H]].
    repeat (destruct p as [|? p]; simpl in H; try discriminate).
  }

  (* 5. "xxxAAA" - keep *)
  apply filter_keep.
  { exists "", "AAA". reflexivity. }

  (* 6. "xxx" - keep *)
  apply filter_keep.
  { exists "", "". reflexivity. }

  (* Base case *)
  apply filter_nil.
Qed.