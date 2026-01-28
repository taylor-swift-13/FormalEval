Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.

Fixpoint prefix (p s : string) : bool :=
  match p with
  | EmptyString => true
  | String c p' =>
      match s with
      | EmptyString => false
      | String c' s' => if Ascii.eqb c c' then prefix p' s' else false
      end
  end.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Example test_filter_by_prefix : filter_by_prefix_spec ["world"; "heworldlo"; "house"] "h" ["heworldlo"; "house"].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.