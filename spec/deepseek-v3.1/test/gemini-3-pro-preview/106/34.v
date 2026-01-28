Require Import List ZArith PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial_nat n'
  end.

Definition factorial (n : Z) : Z := factorial_nat (Z.to_nat n).

Fixpoint sum_to_n_nat (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_to_n_nat n'
  end.

Definition sum_to_n (n : Z) : Z := sum_to_n_nat (Z.to_nat n).

Definition f_spec (n : Z) (result : list Z) : Prop :=
  result = map (fun i => if Z.even i then factorial i else sum_to_n i) 
               (map Z.of_nat (seq 1 (Z.to_nat n))).

Example test_case_proof : f_spec 14 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200].
Proof.
  unfold f_spec.
  vm_compute.
  reflexivity.
Qed.