Require Import List ZArith PeanoNat.
Import ListNotations.

Open Scope Z_scope.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial n'
  end.

Fixpoint sum_to_n (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_to_n n'
  end.

Definition f_spec (n : Z) (result : list Z) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 (Z.to_nat n)).

Example test_case_proof : f_spec 20 [1%Z; 2%Z; 6%Z; 24%Z; 15%Z; 720%Z; 28%Z; 40320%Z; 45%Z; 3628800%Z; 66%Z; 479001600%Z; 91%Z; 87178291200%Z; 120%Z; 20922789888000%Z; 153%Z; 6402373705728000%Z; 190%Z; 2432902008176640000%Z].
Proof.
  unfold f_spec.
  vm_compute.
  reflexivity.
Qed.