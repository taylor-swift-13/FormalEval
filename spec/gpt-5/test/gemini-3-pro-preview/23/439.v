Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_newlines : strlen_spec ("f" ++ String (ascii_of_nat 10) (String (ascii_of_nat 10) "fnunc")) 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.