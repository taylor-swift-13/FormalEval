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
  problem_128_spec [1%Z; 2%Z; 3%Z; 4%Z; -6%Z; -7%Z; -8%Z; -9%Z; -10%Z] (Some (-50%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;2;3;4;-6;-7;-8;-9;-10] = [1;2;3;4;6;7;8;9;10] *)
  (* sum_mags = 1+2+3+4+6+7+8+9+10 = 50 *)
  (* map Z.sgn [1;2;3;4;-6;-7;-8;-9;-10] = [1;1;1;1;-1;-1;-1;-1;-1] *)
  (* prod_sgs = 1*1*1*1*(-1)*(-1)*(-1)*(-1)*(-1) = (1)*((-1)^5) = -1 *)
  (* output = Some (50 * -1) = Some (-50) *)
  reflexivity.
Qed.