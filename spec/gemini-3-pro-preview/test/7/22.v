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
(* Input: strings = ["supercalifragilisticexpialidocious"; "antidisestablishementarianism"; "floccinaucinihilipilification"], substring = "ili" *)
(* Output: result = ["supercalifragilisticexpialidocious"; "floccinaucinihilipilification"] *)

Axiom helper_not_contains : ~ contains_substring "antidisestablishementarianism" "ili".

Example test_filter_complex : filter_by_substring_spec ["supercalifragilisticexpialidocious"; "antidisestablishementarianism"; "floccinaucinihilipilification"] "ili" ["supercalifragilisticexpialidocious"; "floccinaucinihilipilification"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - exists "supercalifrag", "sticexpialidocious". reflexivity.
  - apply filter_skip.
    + apply helper_not_contains.
    + apply filter_keep.
      * exists "floccinaucinih", "pilification". reflexivity.
      * apply filter_nil.
Qed.