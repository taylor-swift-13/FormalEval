Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_woodchuck :
  concatenate_spec ["How"; "much"; "wowod"; "would"; "a"; "woodchuock"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "🐯"; "wood"] "Howmuchwowodwouldawoodchuockchuckifawoodchuckcouldchuck🐯wood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.