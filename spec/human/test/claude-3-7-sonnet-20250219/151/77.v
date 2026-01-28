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

Example test_list_0_3_1_5_5_5 :
  problem_151_spec [0%Z; 3%Z; 1%Z; 5%Z; 5%Z; 5%Z] 85%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  reflexivity.
Qed.