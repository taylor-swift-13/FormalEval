Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Definition s_dian : string := 
  String (ascii_of_nat 231) (String (ascii_of_nat 148) (String (ascii_of_nat 181) EmptyString)).

Definition s_dian_facetious : string := s_dian ++ "facetious".

Example test_filter_by_prefix_dian : 
  filter_by_prefix_spec [s_dian_facetious; s_dian] s_dian [s_dian_facetious; s_dian].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.