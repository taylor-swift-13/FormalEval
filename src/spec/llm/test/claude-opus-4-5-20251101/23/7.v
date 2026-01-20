Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "This is a long string that has many characters in it" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.