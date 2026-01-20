Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_test : strlen_spec "1o, Woorld!890" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.