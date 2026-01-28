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
(* Input: strings = ["supercalifragilisticexpialidocious"; "antidisesshmentarianism"; "floccinaucinihilipilification"; "floccinaucinihilipilificatnion"; "floccinaucinihilipilificatilinion"], substring = "ili" *)
(* Output: result = ["supercalifragilisticexpialidocious"; "floccinaucinihilipilification"; "floccinaucinihilipilificatnion"; "floccinaucinihilipilificatilinion"] *)

Ltac solve_not_contains :=
  let H := fresh "H" in
  let p := fresh "p" in
  let s := fresh "s" in
  intro H; destruct H as [p [s H]];
  repeat (
    destruct p; simpl in H;
    [ discriminate
    | inversion H; subst; clear H;
      match goal with
      | [ H' : _ = _ |- _ ] => rename H' into H
      end
    ]
  ).

Example test_filter_complex : filter_by_substring_spec 
  ["supercalifragilisticexpialidocious"; "antidisesshmentarianism"; "floccinaucinihilipilification"; "floccinaucinihilipilificatnion"; "floccinaucinihilipilificatilinion"] 
  "ili" 
  ["supercalifragilisticexpialidocious"; "floccinaucinihilipilification"; "floccinaucinihilipilificatnion"; "floccinaucinihilipilificatilinion"].
Proof.
  unfold filter_by_substring_spec.
  
  apply filter_keep.
  { exists "supercalifrag", "sticexpialidocious". reflexivity. }
  
  apply filter_skip.
  { solve_not_contains. }
  
  apply filter_keep.
  { exists "floccinaucinih", "pilification". reflexivity. }
  
  apply filter_keep.
  { exists "floccinaucinih", "pilificatnion". reflexivity. }
  
  apply filter_keep.
  { exists "floccinaucinih", "pilificatilinion". reflexivity. }
  
  apply filter_nil.
Qed.