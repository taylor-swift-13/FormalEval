Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "w1This is a sample sstrintog ton test the functiont" 51.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.