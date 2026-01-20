Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_qukick : strlen_spec "Qukick" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.