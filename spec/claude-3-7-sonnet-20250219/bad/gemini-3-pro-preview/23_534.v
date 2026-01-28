Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "     \227          \224\232\236\242\249\225DogttcricQukDogickn\233\237\243\250\236\253\226\234\238\244stwhy1Ngrsr1ng\251\227\241\245\228\235\239\246\252\255\231  " 78.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.