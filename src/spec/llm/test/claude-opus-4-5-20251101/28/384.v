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
  concatenate_spec ["Hw"; "How"; "much"; "woHwod"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "woood"] "HwHowmuchwoHwodwouldawoodchuckchuckifawoodchuckcouldwoood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.