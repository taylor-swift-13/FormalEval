Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "mThftGqorZJum5ymb0lsmtstricQukicknops" 37.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.