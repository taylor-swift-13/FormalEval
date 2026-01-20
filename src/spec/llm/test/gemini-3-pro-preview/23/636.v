Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_sample : strlen_spec "This is a sample strintog ton test the function" 47.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.