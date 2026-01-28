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
  problem_128_spec [1%Z; -4%Z; 3%Z; 17%Z; 5%Z; -6%Z; -8%Z; -9%Z; -7%Z; -6%Z] (Some 66%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1; -4; 3; 17; 5; -6; -8; -9; -7; -6] = [1; 4; 3; 17; 5; 6; 8; 9; 7; 6] *)
  (* sum_mags = 1 + 4 + 3 + 17 + 5 + 6 + 8 + 9 + 7 + 6 = 66 *)
  (* map Z.sgn [1; -4; 3; 17; 5; -6; -8; -9; -7; -6] = [1; -1; 1; 1; 1; -1; -1; -1; -1; -1] *)
  (* prod_sgs = 1 * -1 * 1 * 1 * 1 * -1 * -1 * -1 * -1 * -1 = 1 *)
  (* output = Some (66 * 1) = Some 66 *)
  reflexivity.
Qed.