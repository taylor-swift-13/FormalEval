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

Example test_list_0_3_1_5_1 :
  problem_151_spec [0%Z; 3%Z; 1%Z; 5%Z; 1%Z] 36%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Evaluate the fold step by step:
     Start with acc = 0
     h=0: Z.leb 0 0 = true, Z.odd 0 = false → acc = 0
     h=3: Z.leb 0 3 = true, Z.odd 3 = true → acc = 0 + 3*3 = 9
     h=1: Z.leb 0 1 = true, Z.odd 1 = true → acc = 9 + 1*1 = 10
     h=5: Z.leb 0 5 = true, Z.odd 5 = true → acc = 10 + 25 = 35
     h=1: Z.leb 0 1 = true, Z.odd 1 = true → acc = 35 + 1 = 36
  *)
  reflexivity.
Qed.