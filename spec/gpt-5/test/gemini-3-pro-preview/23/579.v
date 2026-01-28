Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec (String (ascii_of_nat 32) (String (ascii_of_nat 224) (String (ascii_of_nat 232) (String (ascii_of_nat 236) (String (ascii_of_nat 242) (String (ascii_of_nat 104) (String (ascii_of_nat 32) (String (ascii_of_nat 32) EmptyString)))))))) 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.