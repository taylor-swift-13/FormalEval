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

Example test_list_1_2_3_5_5_6 :
  problem_151_spec [1%Z; 2%Z; 3%Z; 5%Z; 5%Z; 6%Z] 60%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* step through fold_left computation:
     acc starts at 0
     1: 1 >= 0 and odd -> acc = 0 + 1*1 = 1
     2: 2 >= 0 but not odd -> acc = 1
     3: 3 >= 0 and odd -> acc = 1 + 3*3 = 10
     5: 5 >= 0 and odd -> acc = 10 + 25 = 35
     5: 5 >= 0 and odd -> acc = 35 + 25 = 60
     6: 6 >= 0 but not odd -> acc = 60
  *)
  reflexivity.
Qed.