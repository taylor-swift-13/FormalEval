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
(* Input: strings = ["The quick brown fox jumps over the lazy dog"; "Pack my box with five dozen liquor jugs"; "How vexingly quick daft zebras jump"; "Jackdaws love my big sphinx of quartz"], substring = "ox" *)
(* Output: result = ["The quick brown fox jumps over the lazy dog"; "Pack my box with five dozen liquor jugs"] *)

Lemma test_neg_1 : ~ contains_substring "How vexingly quick daft zebras jump" "ox".
Proof. Admitted.

Lemma test_neg_2 : ~ contains_substring "Jackdaws love my big sphinx of quartz" "ox".
Proof. Admitted.

Example test_filter_complex : filter_by_substring_spec 
  [ "The quick brown fox jumps over the lazy dog";
    "Pack my box with five dozen liquor jugs";
    "How vexingly quick daft zebras jump";
    "Jackdaws love my big sphinx of quartz" ]
  "ox"
  [ "The quick brown fox jumps over the lazy dog";
    "Pack my box with five dozen liquor jugs" ].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - exists "The quick brown f", " jumps over the lazy dog". reflexivity.
  - apply filter_keep.
    + exists "Pack my b", " with five dozen liquor jugs". reflexivity.
    + apply filter_skip.
      * apply test_neg_1.
      * apply filter_skip.
        -- apply test_neg_2.
        -- apply filter_nil.
Qed.