Require Import List.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1%nat (length xs - 1)%nat).

Example test_derivative : derivative_spec 
  [1%Z; 0%Z; -1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -7%Z; 0%Z; 10%Z; 0%Z; 1%Z; 0%Z] 
  [0%Z; -2%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; -70%Z; 0%Z; 120%Z; 0%Z; 14%Z; 0%Z].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.