Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_testing_string : strlen_spec "Testing testing 123" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.