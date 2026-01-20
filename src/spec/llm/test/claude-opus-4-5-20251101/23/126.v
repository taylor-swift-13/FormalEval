Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_sample_string : strlen_spec "    This is a sampleto string to test the function          " 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.