Require Import List ZArith PeanoNat.
Import ListNotations.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint sum_to_n (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_to_n n'
  end.

Definition f_spec (n : nat) (result : list nat) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 n).

Example test_case_nat : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  vm_compute.
  reflexivity.
Qed.

Example test_case_Z :
  map Z.of_nat (map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 5))
  = [1%Z; 2%Z; 6%Z; 24%Z; 15%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.