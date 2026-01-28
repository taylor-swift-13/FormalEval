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
  problem_151_spec [0%Z; 1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -6%Z; 4%Z; 0%Z] 35%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Calculate each step:
     start acc = 0
     0: 0 >= 0 && 0 odd? 0 is even -> no add, acc = 0
     1: 1 >=0 && odd -> 1*1=1, acc=0+1=1
     2: 2 >=0 & even -> no add, acc=1
     3: 3>=0 & odd -> 9, acc=1+9=10
     4: even -> no add, acc=10
     5: odd & >=0 -> 25, acc=10+25=35
     -6: negative -> no add, acc=35
     4: even -> no add, acc=35
     0: even -> no add, acc=35
  *)
  reflexivity.
Qed.