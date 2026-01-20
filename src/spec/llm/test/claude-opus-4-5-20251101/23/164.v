Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_func_string : strlen_spec "func" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.