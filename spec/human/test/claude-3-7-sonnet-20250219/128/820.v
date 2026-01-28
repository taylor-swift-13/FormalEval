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
  problem_128_spec [-6%Z; 3%Z; 12%Z; -5%Z; -2%Z; -7%Z] (Some 35%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [-6;3;12;-5;-2;-7] = [6;3;12;5;2;7] *)
  (* sum_mags = 6 + 3 + 12 + 5 + 2 + 7 = 35 *)
  (* map Z.sgn [-6;3;12;-5;-2;-7] = [-1;1;1;-1;-1;-1] *)
  (* prod_sgs = (-1) * 1 * 1 * (-1) * (-1) * (-1) = 1 *)
  (* output = Some (35 * 1) = Some 35 *)
  reflexivity.
Qed.