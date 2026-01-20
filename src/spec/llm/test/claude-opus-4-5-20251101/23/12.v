Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_ten_chars : strlen_spec "1234567890" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.