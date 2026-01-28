Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec ("  Lazy " ++ String (ascii_of_nat 10) " Th!s 1s 4 str1ng w1th 5ymb0ls !n 1testt1tt Over The TBrowMNhqmnrownisgmCVstrC1ng 1s") 92.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.