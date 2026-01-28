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
(* Input: strings = ["abcdefg"], substring = "universally" *)
(* Output: result = [] *)

Example test_filter_no_match : filter_by_substring_spec ["abcdefg"] "universally" [].
Proof.
  unfold filter_by_substring_spec.
  apply filter_skip.
  - unfold contains_substring.
    intros [prefix [suffix H]].
    simpl in H.
    (* Prove that "universally" is not a substring of "abcdefg" by structural exhaustion *)
    do 10 (destruct prefix; simpl in H; try discriminate; try (injection H as _ H)).
  - apply filter_nil.
Qed.