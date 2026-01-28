Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix_complex : filter_by_prefix_spec 
  ["apple"; "application"; "airport"; "alligator"; "alphabet"; "ampoule"; "amazon"; "amorous"; "amaze"; "ampABCersand"; "ampersand"; "amputee"; "ambulance"; "amiable"; "butter"; "budget"; "buds"; "bureaucracy"; "burgher"; "business"; "burrow"; "build"; "bully"; "faceless"; "bulge"; "bulb"; "bulldog"; "burdock"]
  "bu"
  ["butter"; "budget"; "buds"; "bureaucracy"; "burgher"; "business"; "burrow"; "build"; "bully"; "bulge"; "bulb"; "bulldog"; "burdock"].
Proof.
  unfold filter_by_prefix_spec.
  reflexivity.
Qed.