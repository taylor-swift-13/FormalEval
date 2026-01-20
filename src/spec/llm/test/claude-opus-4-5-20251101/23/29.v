Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_123345 : strlen_spec "123345" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.