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
  problem_128_spec [2%Z; -8%Z; 0%Z; -7%Z; -6%Z; 16%Z; -8%Z; -8%Z] (Some 0%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [2; -8; 0; -7; -6; 16; -8; -8] = [2;8;0;7;6;16;8;8] *)
  (* sum_mags = 2 + 8 + 0 + 7 + 6 + 16 + 8 + 8 = 55 *)
  (* map Z.sgn [2; -8; 0; -7; -6; 16; -8; -8] = [1; -1; 0; -1; -1; 1; -1; -1] *)
  (* prod_sgs = 1 * (-1) * 0 * (-1) * (-1) * 1 * (-1) * (-1) = 0 *)
  (* output = Some (55 * 0) = Some 0 *)
  reflexivity.
Qed.