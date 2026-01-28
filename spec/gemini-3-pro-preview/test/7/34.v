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
(* Input: strings = ["abc"; "bcd"; "cbd"; "dbc"; "cda"; "cfloccinaucinihilipilificatilinionda"; "dcbd"; "cfloaccinaucinihilipilificatilinionda"], substring = "bbc" *)
(* Output: result = [] *)

Example test_filter_complex : filter_by_substring_spec ["abc"; "bcd"; "cbd"; "dbc"; "cda"; "cfloccinaucinihilipilificatilinionda"; "dcbd"; "cfloaccinaucinihilipilificatilinionda"] "bbc" [].
Proof.
  unfold filter_by_substring_spec.
  repeat (
    match goal with
    | [ |- FilterRel _ [] [] ] => apply filter_nil
    | [ |- FilterRel _ (_ :: _) _ ] => 
        apply filter_skip; [
          unfold contains_substring; intros [p [s H]];
          repeat (destruct p as [|? p]; simpl in H; try discriminate; try (injection H as _ H))
        | ]
    end
  ).
Qed.