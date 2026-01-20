Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "functontMNhqThLe CQuDogmCVnsampBrownleLazyick Brown Fox oJutesttmps OqveThT     testt1t 1 The    iMNhq1TMNMNhqTheher The BrownLazy DàèìòùáéíBrMNhqTheóúýâêîôûãñõäëïöüÿçogmCV" 198.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.