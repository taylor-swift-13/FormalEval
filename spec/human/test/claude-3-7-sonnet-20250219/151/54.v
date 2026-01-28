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

Example test_example_list :
  problem_151_spec [1%Z; 2%Z; 3%Z; 2%Z; 5%Z; 5%Z; 7%Z] 109%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* evaluate fold_left manually *)
  (* fold_left step by step:
     acc = 0
     h = 1: 1 >= 0 and odd -> acc = 0 + 1*1 = 1
     h = 2: 2 >=0 but even -> acc = 1
     h = 3: 3 >=0 and odd -> acc = 1 + 9 = 10
     h = 2: even -> acc = 10
     h = 5: odd -> acc = 10 + 25 = 35
     h = 5: odd -> acc = 35 + 25 = 60
     h = 7: odd -> acc = 60 + 49 = 109
  *)
  reflexivity.
Qed.