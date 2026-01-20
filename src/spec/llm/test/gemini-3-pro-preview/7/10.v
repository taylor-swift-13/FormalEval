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
(* Input: strings = ["123"; "456"; "789"; "101112"], substring = "12" *)
(* Output: result = ["123"; "101112"] *)

Example test_filter_basic : filter_by_substring_spec ["123"; "456"; "789"; "101112"] "12" ["123"; "101112"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - exists "", "3". simpl. reflexivity.
  - apply filter_skip.
    + intros [p [s H]].
      repeat (destruct p; simpl in H; try discriminate; inversion H; subst).
    + apply filter_skip.
      * intros [p [s H]].
        repeat (destruct p; simpl in H; try discriminate; inversion H; subst).
      * apply filter_keep.
        -- exists "1011", "". simpl. reflexivity.
        -- apply filter_nil.
Qed.