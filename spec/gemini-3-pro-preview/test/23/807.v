Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_case1 : strlen_spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintog to test the functiongmCV" 106.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.