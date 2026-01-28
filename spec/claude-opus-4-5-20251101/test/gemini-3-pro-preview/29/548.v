Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Fixpoint starts_with (prefix s : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if Ascii.eqb c1 c2 then starts_with rest1 rest2 else false
  | String _ _, EmptyString => false
  end.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (result : list string) : Prop :=
  result = filter (fun s => starts_with prefix s) strings.

Example test_filter_by_prefix_new : filter_by_prefix_spec ["apple"; "application"; "airport"; "alligator"; "alphabet"; "ampoule"; "amazon"; "amorous"; "amaze"; "ampersand"; "amputee"; "ambulance"; "amiable"; "butter"; "budget"; "businsess"; "buds"; "bureaucracy"; "burgher"; "business"; "burrow"; "build"; "bully"; "faceless"; "bulge"; "bulb"; "bulldog"; "burdock"] "belderberry" [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.