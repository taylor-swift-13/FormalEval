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
  concatenate_spec ["How"; "much"; "wood"; "would"; "🦌a"; "woodchuck"; "chuck"; "if"; "would"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "chuck"; "woodchuck"; "much"; "Hw"; "chuck"] "Howmuchwoodwould🦌awoodchuckchuckifwouldawoodchuckcouldchuckwoodchuckwoodchuckmuchHwchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.