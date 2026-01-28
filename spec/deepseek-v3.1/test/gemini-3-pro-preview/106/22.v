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

Example test_case_proof : f_spec 13 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91].
Proof.
  unfold f_spec.
  vm_compute.
  reflexivity.
Qed.