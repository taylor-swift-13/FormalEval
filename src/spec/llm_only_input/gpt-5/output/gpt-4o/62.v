Require Import List.
Require Import Nat.
Require Import ZArith.

Import ListNotations.

Local Open Scope nat_scope.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => (nth i xs 0%nat * i)%nat) (seq 1%nat (length xs - 1)%nat).

Open Scope Z_scope.

Definition derivative_spec_Z (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => (nth i xs 0%Z) * Z.of_nat i) (seq 1%nat (length xs - 1)%nat).

Example derivative_spec_test_Z :
  derivative_spec_Z [3%Z; 1%Z; 2%Z; 4%Z; 5%Z] [1%Z; 4%Z; 12%Z; 20%Z].
Proof.
  unfold derivative_spec_Z.
  vm_compute.
  reflexivity.
Qed.