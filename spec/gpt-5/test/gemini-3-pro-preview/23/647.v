Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "BrowMNhqThe CQuick Brown Fstrintogwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazy" 87.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.