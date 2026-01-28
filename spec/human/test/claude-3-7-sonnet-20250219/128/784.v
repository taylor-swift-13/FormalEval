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
  problem_128_spec [4%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 2%Z; 3%Z; 4%Z; -1%Z; -2%Z; -3%Z; -4%Z; 6%Z; 7%Z; -5%Z; -6%Z; -7%Z] (Some 0%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [4;0;0;0;0;0;1;2;3;4;-1;-2;-3;-4;6;7;-5;-6;-7] = [4;0;0;0;0;0;1;2;3;4;1;2;3;4;6;7;5;6;7] *)
  (* sum_mags = 4+0+0+0+0+0+1+2+3+4+1+2+3+4+6+7+5+6+7 = 55 *)
  (* map Z.sgn [4;0;0;0;0;0;1;2;3;4;-1;-2;-3;-4;6;7;-5;-6;-7] = [1;0;0;0;0;0;1;1;1;1;-1;-1;-1;-1;1;1;-1;-1;-1] *)
  (* product includes zero factors, so prod_sgs = 0 *)
  (* output = Some (55 * 0) = Some 0 *)
  reflexivity.
Qed.