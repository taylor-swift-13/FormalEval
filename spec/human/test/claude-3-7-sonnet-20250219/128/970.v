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
  problem_128_spec [3%Z; 13%Z; 1%Z; 3%Z; -4%Z; 3%Z] (Some (-27%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [3;13;1;3;-4;3] = [3;13;1;3;4;3] *)
  (* sum_mags = 3 + 13 + 1 + 3 + 4 + 3 = 27 *)
  (* map Z.sgn [3;13;1;3;-4;3] = [1;1;1;1;-1;1] *)
  (* prod_sgs = 1 * 1 * 1 * 1 * (-1) * 1 = -1 *)
  (* output = Some (27 * -1) = Some (-27) *)
  reflexivity.
Qed.