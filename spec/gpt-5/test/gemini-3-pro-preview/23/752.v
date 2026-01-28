Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "s    

 !func!ntion  e" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.