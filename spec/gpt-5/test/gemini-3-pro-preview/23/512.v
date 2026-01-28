Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "vemThfGqorZJum5ymb0lsmtstgrsr1ngLqNCZAtestpsr" 45.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.