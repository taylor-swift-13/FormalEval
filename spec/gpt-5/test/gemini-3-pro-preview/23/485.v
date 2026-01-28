Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukDogickn      4!n 

  1s  " 90.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.