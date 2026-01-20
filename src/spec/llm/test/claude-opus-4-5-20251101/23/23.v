Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_eleven_chars : strlen_spec "11234567890" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.