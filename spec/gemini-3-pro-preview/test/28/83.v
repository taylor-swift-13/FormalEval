Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["Rock"; "orangeoran456ge"; "Scisi456bananasoors"; "Scissoors"] "Rockorangeoran456geScisi456bananasoorsScissoors".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.