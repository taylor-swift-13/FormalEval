Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition problem_128_pre (arr : list Z) : Prop := True.

Definition problem_128_spec (arr : list Z) (output : option Z) : Prop :=
  match arr with
  | [] => output = None
  | _ :: _ =>
    let sum_mags := fold_right Z.add 0 (map Z.abs arr) in
    let prod_sgs := fold_right Z.mul 1 (map Z.sgn arr) in
    output = Some (sum_mags * prod_sgs)
  end.

Example problem_128_test1 :
  problem_128_spec [4%Z; -7%Z; 6%Z; -2%Z; -3%Z; -4%Z; -5%Z; -6%Z; -7%Z; -8%Z; -9%Z; -3%Z; -11%Z] (Some (-75%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [4; -7; 6; -2; -3; -4; -5; -6; -7; -8; -9; -3; -11] = [4; 7; 6; 2; 3; 4; 5; 6; 7; 8; 9; 3; 11] *)
  (* sum_mags = 4+7+6+2+3+4+5+6+7+8+9+3+11 = 75 *)
  (* map Z.sgn [4; -7; 6; -2; -3; -4; -5; -6; -7; -8; -9; -3; -11] = [1; -1; 1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1] *)
  (* prod_sgs = 1 * (-1) * 1 * (-1) * (-1) * (-1) * (-1) * (-1) * (-1) * (-1) * (-1) * (-1) * (-1) *)
  (* Count of negative signs = 11, so product is (-1)^11 = -1 *)
  (* output = Some (75 * -1) = Some (-75) *)
  reflexivity.
Qed.