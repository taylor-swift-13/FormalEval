Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Juom5This is a sample string    This is a sampl            eto string to test the func Theon       to test the functionymbops" 125.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.