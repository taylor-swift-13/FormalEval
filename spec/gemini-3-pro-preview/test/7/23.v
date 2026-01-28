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
(* Input: strings = ["abc"; "bcd"; "cbd"; "dbc"; "cda"; "cfloccinaucinihilipilificatilinionda"], substring = "bc" *)
(* Output: result = ["abc"; "bcd"; "dbc"] *)

Ltac solve_not_contains :=
  let H := fresh "H" in
  let p := fresh "p" in
  let s := fresh "s" in
  intro H; destruct H as [p [s H]];
  repeat (
    destruct p; simpl in H;
    [ discriminate
    | try discriminate; injection H as _ H ]
  ).

Example test_filter_complex : filter_by_substring_spec ["abc"; "bcd"; "cbd"; "dbc"; "cda"; "cfloccinaucinihilipilificatilinionda"] "bc" ["abc"; "bcd"; "dbc"].
Proof.
  unfold filter_by_substring_spec.
  apply filter_keep.
  { exists "a", "". reflexivity. }
  apply filter_keep.
  { exists "", "d". reflexivity. }
  apply filter_skip.
  { solve_not_contains. }
  apply filter_keep.
  { exists "d", "". reflexivity. }
  apply filter_skip.
  { solve_not_contains. }
  apply filter_skip.
  { solve_not_contains. }
  apply filter_nil.
Qed.