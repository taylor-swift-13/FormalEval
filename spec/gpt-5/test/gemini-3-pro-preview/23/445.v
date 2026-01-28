Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukDogickn" 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.