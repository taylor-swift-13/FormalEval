Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "     ã          àèìòùáDogttcricQukDogicknéíóúìýâêîôstwhy1Ngrsr1ngûãñõäëïöüÿç  " 106.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.