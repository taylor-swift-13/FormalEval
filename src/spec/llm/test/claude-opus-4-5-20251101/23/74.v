Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_test_string : strlen_spec "Test1iTng testing 123" 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.