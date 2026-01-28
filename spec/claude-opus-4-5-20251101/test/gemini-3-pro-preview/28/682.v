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

Example test_concatenate_example: concatenate_spec ["123"; "456"; "789"; "🦌"; "11"; "12"; "13"; "14"; "133"; "16"; "without"; "18"; "13"; "133"; "12"; "12"] "123456789🦌1112131413316without18131331212".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.