Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition problem_151_pre (l : list Z) : Prop := True.

Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

Example test_problem_151_0 : problem_151_spec [2; 3; 6; -7; 11; 12; -13; 17; 18; -7; -20; -14; 21] 860.
Proof.
  unfold problem_151_spec.
  vm_compute.
  reflexivity.
Qed.