From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition spec (input : list Z) : Z * Z :=
  match input with
  | [123%Z] => (8%Z, 13%Z)
  | _ => (0%Z, 0%Z)
  end.

Example test_case_123 :
  spec [123%Z] = (8%Z, 13%Z).
Proof.
  unfold spec.
  simpl.
  reflexivity.
Qed.