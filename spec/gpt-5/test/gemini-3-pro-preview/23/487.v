Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
um5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test           àèìòùáéíóúýâêîôûãñõäëïöüÿçQuaOverick     s" 191.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.