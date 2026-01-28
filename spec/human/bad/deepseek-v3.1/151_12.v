Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Reals.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_151_spec (l : list R) (res : Z) : Prop :=
  res = fold_left (fun acc h => 
                       if (Z.leb 0 (Z.of_nat (Z.floor h))) && (Z.odd (Z.of_nat (Z.floor h)))
                       then Z.add acc (Z.mul (Z.of_nat (Z.floor h)) (Z.of_nat (Z.floor h)))
                       else acc) l 0.

Example test_case_151 : problem_151_spec [[1.0%R; 3.5%R; -4.6%R]] 0.
Proof.
  unfold problem_151_spec.
  simpl.
  reflexivity.
Qed.