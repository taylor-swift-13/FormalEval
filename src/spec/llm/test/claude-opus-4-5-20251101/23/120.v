Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_spaces_newlines : strlen_spec "   

 1s  " 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.