Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_str1ng : strlen_spec "str1ng" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.