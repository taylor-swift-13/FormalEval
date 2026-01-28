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

Example test_neg_pos_odd_squares :
  problem_151_spec [-5%Z; 7%Z; 9%Z] 130%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Evaluate fold_left step-by-step *)
  (* acc = 0 *)
  (* For h = -5: Z.leb 0 (-5) = false, so acc remains 0 *)
  (* For h = 7: Z.leb 0 7 = true, Z.odd 7 = true, so acc = 0 + 7*7 = 49 *)
  (* For h = 9: Z.leb 0 9 = true, Z.odd 9 = true, so acc = 49 + 9*9 = 49 + 81 = 130 *)
  reflexivity.
Qed.