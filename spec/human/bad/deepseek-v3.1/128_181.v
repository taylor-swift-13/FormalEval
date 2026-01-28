Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition problem_128_spec (arr : list Z) (output : option Z) : Prop :=
  match arr with
  | [] => output = None
  | _ :: _ =>
    let sum_mags := fold_right Z.add 0 (map Z.abs arr) in
    let prod_sgs := fold_right Z.mul 1 (map Z.sgn arr) in
    output = Some (sum_mags * prod_sgs)
  end.

Example test_case_2 : problem_128_spec [1; -3; -4; 0; 5; 6; -7; -8; 9; 10; 11; -12; 13; 14; -15; 16; 17; -18; -19; -20; 0] (Some 0).
Proof.
  unfold problem_128_spec.
  simpl.
  rewrite Z.mul_1_l.
  rewrite Z.mul_0_r.
  reflexivity.
Qed.