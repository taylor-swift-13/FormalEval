Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_p1s4Bnrown : strlen_spec "p1s4Bnrown" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.