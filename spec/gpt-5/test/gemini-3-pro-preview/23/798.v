Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "MNhqThe CQu			ick Brown func!ntionFox oJutesttmps Over The BrownLazy DogmCV" 75.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.