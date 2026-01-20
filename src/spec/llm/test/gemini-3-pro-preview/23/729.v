Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_nonzero : strlen_spec "BwownLazyLazy  " 15.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.