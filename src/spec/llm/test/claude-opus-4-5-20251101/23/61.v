Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_off_foiivfe : strlen_spec "off
foiivfe" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.