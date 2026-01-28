Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukickn      4!n 

  1s  " 87.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.