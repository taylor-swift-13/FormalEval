Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

Example test_case_151 : problem_151_spec [3; 5; 7] 83.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Compute step by step: *)
  (* Start with acc = 0 *)
  (* h=3: 0 + 3*3=9 (since 3≥0 and 3 odd): acc=9 *)
  (* h=5: 9 + 5*5=25: acc=34 *)
  (* h=7: 34 + 7*7=49: acc=83 *)
  reflexivity.
Qed.