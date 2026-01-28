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
  problem_128_spec [1%Z; 3%Z; 3%Z; 4%Z; -2%Z; -2%Z; -1%Z] (Some (-16%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;3;3;4;-2;-2;-1] = [1;3;3;4;2;2;1] *)
  (* sum_mags = 1 + 3 + 3 + 4 + 2 + 2 + 1 = 16 *)
  (* map Z.sgn [1;3;3;4;-2;-2;-1] = [1;1;1;1;-1;-1;-1] *)
  (* prod_sgs = 1 * 1 * 1 * 1 * (-1) * (-1) * (-1) = -1 *)
  (* output = Some (16 * -1) = Some (-16) *)
  reflexivity.
Qed.