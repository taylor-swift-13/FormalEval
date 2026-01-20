Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_newline : strlen_spec ("oef" ++ String (ascii_of_nat 10) "ffoive") 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.