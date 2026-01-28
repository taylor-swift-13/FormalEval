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

Example test_non_empty_list :
  problem_151_spec [3%Z; 5%Z; 7%Z] 83%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  unfold Z.leb, Z.odd.
  (* Let's reduce the condition step by step *)
  (* 0 <= 3 is true, 3 odd is true, so acc = 0 + 3*3 = 9 *)
  (* 0 <= 5 is true, 5 odd is true, acc = 9 + 5*5 = 9 + 25 = 34 *)
  (* 0 <= 7 is true, 7 odd is true, acc = 34 + 49 = 83 *)
  reflexivity.
Qed.