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

Example test_case_1 :
  problem_151_spec [2%Z; 3%Z; 4%Z; 5%Z] 34%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Computation steps: 
     acc = 0
     h = 2: 2 >= 0 true, 2 odd? false, acc stays 0
     h = 3: 3 >= 0 true, 3 odd? true, acc = 0 + 9 = 9
     h = 4: 4 >= 0 true, 4 odd? false, acc = 9
     h = 5: 5 >= 0 true, 5 odd? true, acc = 9 + 25 = 34
  *)
  reflexivity.
Qed.