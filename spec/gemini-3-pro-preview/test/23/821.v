Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_1 : strlen_spec "This is ao sample starintog ton test the n" 42.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.