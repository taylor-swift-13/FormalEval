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
  problem_128_spec [1%Z; 2%Z; -9%Z; -12%Z; 3%Z; -3%Z; -2%Z; -1%Z; 1%Z] (Some (-34%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1; 2; -9; -12; 3; -3; -2; -1; 1] = [1; 2; 9; 12; 3; 3; 2; 1; 1] *)
  (* sum_mags = 1+2+9+12+3+3+2+1+1 = 34 *)
  (* map Z.sgn [1; 2; -9; -12; 3; -3; -2; -1; 1] = [1; 1; -1; -1; 1; -1; -1; -1; 1] *)
  (* prod_sgs = 1*1*(-1)*(-1)*1*(-1)*(-1)*(-1)*1 *)
  (* Two negatives cancel: (-1)*(-1) = 1, so after first four elements prod=1 *)
  (* Continue multiplying remainder: 1*(-1)*(-1)*(-1)*1 *)
  (* (-1)*(-1)=1; 1*1=1; 1*(-1) = -1; -1*1 = -1 *)
  (* Therefore total product = -1 *)
  (* output = Some (34 * -1) = Some (-34) *)
  reflexivity.
Qed.