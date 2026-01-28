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

Example test_nonempty_list :
  problem_151_spec [5%Z; 7%Z; 9%Z; -10%Z; -12%Z] 155%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Calculate step by step *)
  (* fold_left starts with acc = 0 *)
  (* For h = 5: 5 >= 0 true, odd? 5 mod 2 = 1 true *)
  (* acc = 0 + 5*5 = 25 *)
  (* For h = 7: 7 >= 0 true, odd? true *)
  (* acc = 25 + 7*7 = 25 + 49 = 74 *)
  (* For h = 9: 9 >= 0 true, odd? true *)
  (* acc = 74 + 81 = 155 *)
  (* For h = -10: -10 >= 0 false *)
  (* acc stays 155 *)
  (* For h = -12: -12 >= 0 false *)
  (* acc stays 155 *)
  reflexivity.
Qed.