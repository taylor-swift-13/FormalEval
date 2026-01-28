Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_fox_panda_koala_tiger_hippo_18_deer_swan_owl_exclamation_turtle_owl :
  problem_28_spec ["🦊"; "🐼"; "🐨"; "🐯"; "🦛"; "18"; ""; "🦌"; "🦢"; "🦉"; "!!"; "🐢"; "🦉"] "🦊🐼🐨🐯🦛18🦌🦢🦉!!🐢🦉".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.