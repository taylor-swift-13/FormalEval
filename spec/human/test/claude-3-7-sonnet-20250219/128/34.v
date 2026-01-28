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
  problem_128_spec [2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 2%Z; 3%Z; 5%Z; 2%Z; -2%Z] (Some (-24%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* sum_mags = 2+2+2+2+2+2+3+5+2+2 = 24 *)
  (* prod_sgs = 1*1*1*1*1*1*1*1*1*(-1) = -1 *)
  (* output = Some (24 * -1) = Some (-24) *)
  reflexivity.
Qed.