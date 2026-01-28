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
Example test_filter_complex : 
  filter_by_substring_spec 
    ["supercalifragilisticexpialidocious"; "sun"; "floccinaucinihilipilificatioearthn"] 
    "ili" 
    ["supercalifragilisticexpialidocious"; "floccinaucinihilipilificatioearthn"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  - exists "supercalifrag", "sticexpialidocious". reflexivity.
  - apply filter_skip.
    + intros [p [s H]].
      destruct p; simpl in H.
      * discriminate.
      * destruct p; simpl in H.
        { inversion H. }
        { destruct p; simpl in H.
          - inversion H.
          - destruct p; simpl in H; discriminate.
        }
    + apply filter_keep.
      * exists "floccinaucinih", "pilificatioearthn". reflexivity.
      * apply filter_nil.
Qed.