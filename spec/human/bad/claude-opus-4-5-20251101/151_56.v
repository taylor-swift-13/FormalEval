Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Reals.
Require Import Lra.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition problem_151_pre (l : list Z) : Prop := True.

Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

Definition ceil_real (r : R) : Z :=
  if Rlt_dec r 0 then Z.opp (up (Ropp r)) + 1 else up r.

Definition process_real_list (l : list R) : list Z :=
  map (fun r => ceil_real r) l.

Example test_problem_151 : problem_151_spec (process_real_list [(-4.6)%R]) 0%Z.
Proof.
  unfold problem_151_spec.
  unfold process_real_list.
  simpl.
  unfold ceil_real.
  destruct (Rlt_dec (-4.6) 0) as [H|H].
  - simpl.
    assert (Hup: up (- (-4.6)) = 5).
    {
      apply tech_up.
      - lra.
      - lra.
    }
    rewrite Hup.
    simpl.
    reflexivity.
  - exfalso. apply H. lra.
Qed.