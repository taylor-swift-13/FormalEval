Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_newline_string : strlen_spec "This string has a 
 newline character" 37.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.