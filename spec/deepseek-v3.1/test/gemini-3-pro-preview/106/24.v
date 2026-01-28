Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint factorial_aux (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial_aux n'
  end.

Definition factorial (n : Z) : Z :=
  factorial_aux (Z.to_nat n).

Fixpoint sum_to_n_aux (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_to_n_aux n'
  end.

Definition sum_to_n (n : Z) : Z :=
  sum_to_n_aux (Z.to_nat n).

Definition f_spec (n : Z) (result : list Z) : Prop :=
  result = map (fun i => if Z.even (Z.of_nat i) then factorial (Z.of_nat i) else sum_to_n (Z.of_nat i)) (seq 1 (Z.to_nat n)).

Example test_case_proof : f_spec 21 [1; 2; 6; 24; 15; 720; 28; 40320; 45; 3628800; 66; 479001600; 91; 87178291200; 120; 20922789888000; 153; 6402373705728000; 190; 2432902008176640000; 231].
Proof.
  unfold f_spec.
  vm_compute.
  reflexivity.
Qed.