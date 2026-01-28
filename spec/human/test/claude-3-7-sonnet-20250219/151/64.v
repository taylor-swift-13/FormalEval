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

Example test_list_5_4_6_6 :
  problem_151_spec [5%Z; 4%Z; 6%Z; 6%Z] 25%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Evaluate (Z.leb 0 5) && (Z.odd 5) = true && true = true *)
  (* So add 5*5 = 25 to acc 0 *)
  (* Next, 4: (Z.leb 0 4) && (Z.odd 4) = true && false = false, acc stays 25 *)
  (* Next, 6: (Z.leb 0 6) && (Z.odd 6) = true && false = false, acc stays 25 *)
  (* Next, 6 again: same as above, acc still 25 *)
  reflexivity.
Qed.