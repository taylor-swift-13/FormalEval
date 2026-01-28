Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "MNhqThe CQuick Brown Fox Jumps Over The BrownLaz   

   zy DomgmCV" 66.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.