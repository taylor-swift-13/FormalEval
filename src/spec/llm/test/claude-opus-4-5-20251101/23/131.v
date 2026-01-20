Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_tish : strlen_spec "Tish!" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.