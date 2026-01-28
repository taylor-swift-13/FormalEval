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

Example test_input_3_5_7_3 :
  problem_151_spec [3%Z; 5%Z; 7%Z; 3%Z] 92%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Calculate the fold step by step *)
  (* acc = 0 *)
  (* h = 3: 3 >= 0 and odd -> add 3*3=9, acc=9 *)
  (* h = 5: 5 >= 0 and odd -> add 5*5=25, acc=34 *)
  (* h = 7: 7 >= 0 and odd -> add 7*7=49, acc=83 *)
  (* h = 3: 3 >= 0 and odd -> add 3*3=9, acc=92 *)
  reflexivity.
Qed.