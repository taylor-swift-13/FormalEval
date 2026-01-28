Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "ThT     ttestt1t 1 TBrownLazyhe    i" 36.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.