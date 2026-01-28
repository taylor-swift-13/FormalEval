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
  problem_128_spec [-3%Z; 5%Z; -7%Z] (Some 15%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [-3;5;-7] = [3;5;7] *)
  (* sum_mags = 3 + 5 + 7 = 15 *)
  (* map Z.sgn [-3;5;-7] = [-1;1;-1] *)
  (* prod_sgs = (-1) * 1 * (-1) = 1 *)
  (* output = Some (15 * 1) = Some 15 *)
  reflexivity.
Qed.