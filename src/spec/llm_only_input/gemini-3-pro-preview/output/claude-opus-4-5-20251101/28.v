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

(* Test case: input = [[]] (interpreted as a list containing an empty string), output = "" *)
Example test_concatenate_1: concatenate_spec [""] "".
Proof.
  (* Unfold the specification definition *)
  unfold concatenate_spec.
  (* Simplify the execution of the concatenate function *)
  simpl.
  (* Check that the left-hand side equals the right-hand side ("" = "") *)
  reflexivity.
Qed.