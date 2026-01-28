Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintog to test the functiongmCV" 106.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.