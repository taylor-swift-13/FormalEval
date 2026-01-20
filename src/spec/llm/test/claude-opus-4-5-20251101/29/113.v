Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint starts_with (prefix s : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if Ascii.eqb c1 c2 then starts_with rest1 rest2 else false
  | String _ _, EmptyString => false
  end.

Definition filter_by_prefix_spec (strings : list string) (prefix : string) (result : list string) : Prop :=
  result = filter (fun s => starts_with prefix s) strings.

Example test_filter_by_prefix :
  filter_by_prefix_spec ["apple"%string; "application"%string; "airport"%string; "alligator"%string; "alphabet"%string; "ampoule"%string; "amazon"%string; "amorous"%string; "amaze"%string; "ampersand"%string; "amputee"%string; "ambulance"%string; "amiable"%string; "butter"%string; "budget"%string; "buds"%string; "bureaucracy"%string; "burgher"%string; "business"%string; "burrow"%string; "build"%string; "bully"%string; "bulge"%string; "bulb"%string; "bulldog"%string; "burdock"%string; "bulldog"%string] "buu"%string [].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.