Require Import String.
Open Scope string_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_case_1: problem_23_spec "one
twota
thrThis is a long string that has many chone
twot
thrThis is a long string that has  many characters in itee
four
fivearacters in itee
four
five" 154.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.