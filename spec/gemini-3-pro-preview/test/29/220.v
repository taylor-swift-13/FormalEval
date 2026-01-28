Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Definition zi := String (ascii_of_nat 229) (String (ascii_of_nat 173) (String (ascii_of_nat 144) EmptyString)).

Example test_filter_by_prefix_zi : filter_by_prefix_spec [zi] zi [zi].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.