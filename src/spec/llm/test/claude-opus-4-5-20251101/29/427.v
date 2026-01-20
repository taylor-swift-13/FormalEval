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
  filter_by_prefix_spec ["fgh"%string; "Kilometer"%string; "Gigabyte"%string; "Kiwi"%string; "jinx"%string; "jujitsu"%string; "Joyride"%string; "foothills"%string; "filter"%string; "fiduciary"%string; "fidelity"%string; "film"%string; "fault"%string; "fantasy"%string; "fanfare"%string; "cfacetiousfavicon"%string; "fabric"%string; "facetious"%string; "facade"%string; "faceless"%string; "flabbergasted"%string; "foolish"%string; "forward"%string; "forgive"%string; "foliage"%string; "faceless"%string] EmptyString ["fgh"%string; "Kilometer"%string; "Gigabyte"%string; "Kiwi"%string; "jinx"%string; "jujitsu"%string; "Joyride"%string; "foothills"%string; "filter"%string; "fiduciary"%string; "fidelity"%string; "film"%string; "fault"%string; "fantasy"%string; "fanfare"%string; "cfacetiousfavicon"%string; "fabric"%string; "facetious"%string; "facade"%string; "faceless"%string; "flabbergasted"%string; "foolish"%string; "forward"%string; "forgive"%string; "foliage"%string; "faceless"%string].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.