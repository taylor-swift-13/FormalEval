Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "ThT    1sampLazylet 1 The    i" 30.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.