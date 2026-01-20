Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_quick_brown_fox : strlen_spec "The Quick Brown Fox Jumps Over The Lazy Dog" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.