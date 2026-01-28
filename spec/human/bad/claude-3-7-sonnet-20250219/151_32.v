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

Example test_single_list :
  problem_151_spec [-10%Z; 5%Z] 25%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  (* Evaluate the condition for h = -10 *)
  assert (H1 : (Z.leb 0 (-10)) = false).
  { reflexivity. }
  rewrite H1.
  simpl.
  (* Evaluate the condition for h = 5 *)
  assert (H2 : (Z.leb 0 5 = true) /\ (Z.odd 5 = true).
  { split; reflexivity. }
  destruct H2 as [H2a H2b].
  rewrite H2a, H2b.
  simpl.
  reflexivity.
Qed.