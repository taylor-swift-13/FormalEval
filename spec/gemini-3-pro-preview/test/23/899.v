Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_custom : strlen_spec "BrowMNhqThe CQuick Brown Fstrintogwox Jumpes Over The BrownLazuey DogmCVnsampBrownleLazy" 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.