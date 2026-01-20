Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_newline_string : strlen_spec "GNDThis string has a 
 newline characterdEb" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.