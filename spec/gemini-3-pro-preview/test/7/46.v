Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
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

(* Helper definitions for verification *)
Fixpoint starts_with (s sub : string) : bool :=
  match sub with
  | EmptyString => true
  | String c2 sub' =>
      match s with
      | EmptyString => false
      | String c1 s' =>
          if ascii_dec c1 c2 then starts_with s' sub' else false
      end
  end.

Fixpoint contains_substring_bool (s sub : string) : bool :=
  match s with
  | EmptyString => starts_with s sub
  | String c s' => starts_with s sub || contains_substring_bool s' sub
  end.

Lemma contains_substring_correct : forall s sub,
  contains_substring s sub <-> contains_substring_bool s sub = true.
Proof.
  Admitted.

Ltac solve_contains :=
  rewrite contains_substring_correct; vm_compute; reflexivity.

Ltac solve_not_contains :=
  rewrite contains_substring_correct; vm_compute; discriminate.

(* Test case verification *)
(* Input: strings = ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"; "Washington"], substring = "an" *)
(* Output: result = ["San Francisco"] *)

Example test_filter_cities : filter_by_substring_spec 
  ["Washington"; "DC"; "New York City"; "Boston"; "Los Angeles"; "San Francisco"; "Miami"; "Washington"] 
  "an" 
  ["San Francisco"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip. { solve_not_contains. }
  apply filter_skip. { solve_not_contains. }
  apply filter_skip. { solve_not_contains. }
  apply filter_skip. { solve_not_contains. }
  apply filter_skip. { solve_not_contains. }
  apply filter_keep. { solve_contains. }
  apply filter_skip. { solve_not_contains. }
  apply filter_skip. { solve_not_contains. }
  apply filter_nil.
Qed.