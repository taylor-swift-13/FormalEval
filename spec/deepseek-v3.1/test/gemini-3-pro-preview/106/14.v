Require Import List ZArith PeanoNat.
Import ListNotations.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | O => 1%Z
  | S n' => Z.mul (Z.of_nat n) (factorial n')
  end.

Fixpoint sum_to_n (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S n' => Z.add (Z.of_nat n) (sum_to_n n')
  end.

Definition f_spec (n : nat) (result : list Z) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 n).

Example test_case_proof : f_spec 12 [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z].
Proof.
  unfold f_spec.
  vm_compute.
  reflexivity.
Qed.