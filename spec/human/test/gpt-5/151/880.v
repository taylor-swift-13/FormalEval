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

Example problem_151_test_case :
  problem_151_spec [-2%Z; -4%Z; -5%Z; 7%Z; -11%Z; -14%Z; 12%Z; -18%Z; 19%Z; 24%Z; 25%Z; 26%Z; -28%Z; -29%Z; 26%Z; -2%Z] 1035%Z.
Proof.
  unfold problem_151_spec.
  vm_compute.
  reflexivity.
Qed.