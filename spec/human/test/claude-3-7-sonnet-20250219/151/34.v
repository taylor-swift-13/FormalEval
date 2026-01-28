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

Example test_list_1_5 :
  problem_151_spec [1%Z; 5%Z] 26%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* fold_left with acc=0, h=1: 1 >= 0 and odd -> acc := 0 + 1*1 = 1 *)
  (* next h=5: 5 >= 0 and odd -> acc := 1 + 5*5 = 1 + 25 = 26 *)
  reflexivity.
Qed.