Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_three_four_five : strlen_spec "three
four
five" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.