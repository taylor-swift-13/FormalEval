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
  problem_128_spec [1%Z; 2%Z; -9%Z; -13%Z; 3%Z; -19%Z; -2%Z; -2%Z; -20%Z] (Some 71%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;2;-9;-13;3;-19;-2;-2;-20] = [1;2;9;13;3;19;2;2;20] *)
  (* sum_mags = 1 + 2 + 9 + 13 + 3 + 19 + 2 + 2 + 20 = 71 *)
  (* map Z.sgn [1;2;-9;-13;3;-19;-2;-2;-20] = [1;1;-1;-1;1;-1;-1;-1;-1] *)
  (* prod_sgs = 1 * 1 * (-1) * (-1) * 1 * (-1) * (-1) * (-1) * (-1) = 1 *)
  (* output = Some (71 * 1) = Some 71 *)
  reflexivity.
Qed.