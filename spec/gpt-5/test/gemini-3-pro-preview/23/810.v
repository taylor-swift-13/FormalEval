Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "MNMNhqThe CQuick Brown Fox JumpBrownL     
   azyses Over The BrownLazy DogmCV
hCV" 82.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.