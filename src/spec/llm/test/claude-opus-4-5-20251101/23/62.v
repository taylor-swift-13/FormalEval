Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_twelve_chars : strlen_spec "912345667890" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.