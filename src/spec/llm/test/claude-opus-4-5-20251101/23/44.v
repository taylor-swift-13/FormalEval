Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_1223545 : strlen_spec "1223545" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.