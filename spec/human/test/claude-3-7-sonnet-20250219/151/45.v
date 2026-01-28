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

Example test_list_5_7_7_9_minus10_minus12_minus12 :
  problem_151_spec [5%Z; 7%Z; 7%Z; 9%Z; -10%Z; -12%Z; -12%Z] 204%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Evaluate the fold manually: *)
  (* Start with acc = 0 *)
  (* h = 5: 5 >=0 and 5 odd -> acc = 0 + 25 = 25 *)
  (* h = 7: 7 >=0 and 7 odd -> acc = 25 + 49 = 74 *)
  (* h = 7: 7 >=0 and 7 odd -> acc = 74 + 49 = 123 *)
  (* h = 9: 9 >=0 and 9 odd -> acc = 123 + 81 = 204 *)
  (* h = -10: not >=0 -> acc = 204 *)
  (* h = -12: not >=0 -> acc = 204 *)
  (* h = -12: not >=0 -> acc = 204 *)
  reflexivity.
Qed.