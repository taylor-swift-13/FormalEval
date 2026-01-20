Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "   
hy    This is a sample strinisg to test othe fuunction          NcJH
  string4" 82.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.