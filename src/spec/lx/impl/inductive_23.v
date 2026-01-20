(* HumanEval 23 - Inductive Spec *)
Require Import Coq.Strings.String Coq.Arith.Arith.
Open Scope string_scope.

Inductive string_length_rel : string -> nat -> Prop :=
| slr_empty : string_length_rel "" 0%nat
| slr_step : forall c s n, string_length_rel s n -> string_length_rel (String c s) (S n).

Definition strlen_spec (s : string) (output : nat) : Prop :=
  string_length_rel s output.


