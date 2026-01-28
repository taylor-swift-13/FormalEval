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
(* Input: strings = ["abc(d)e"; "ba%cd"; "cde"; "array"; "12345"], substring = "(d)" *)
(* Output: result = ["abc(d)e"] *)

Ltac solve_not_contains :=
  intros [pre [suf H]];
  repeat (destruct pre; simpl in H; try discriminate).

Example test_filter_complex : filter_by_substring_spec ["abc(d)e"; "ba%cd"; "cde"; "array"; "12345"] "(d)" ["abc(d)e"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - exists "abc", "e". reflexivity.
  - apply filter_skip.
    + solve_not_contains.
    + apply filter_skip.
      * solve_not_contains.
      * apply filter_skip.
        -- solve_not_contains.
        -- apply filter_skip.
           ++ solve_not_contains.
           ++ apply filter_nil.
Qed.