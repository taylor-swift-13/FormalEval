Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Rpower.
Open Scope bool_scope.
Open Scope Z_scope.

Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

Example test_case_151 : problem_151_spec [2%Z; 2.5%R; 3%Z; 3.5%R; 4.5%R; 5%Z] 34%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  reflexivity.
Qed.