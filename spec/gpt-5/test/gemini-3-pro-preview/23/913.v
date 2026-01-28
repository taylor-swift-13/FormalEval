Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "BrowMNhqThe CQuick Brown Fstrintogwox Jumpes Over zy" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.