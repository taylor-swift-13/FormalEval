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
  problem_128_spec
    [1%Z; 14%Z; 2%Z; -3%Z; -4%Z; 0%Z; 5%Z; 6%Z; -7%Z; 9%Z; 10%Z; 11%Z; -12%Z; 13%Z; 14%Z; -15%Z; 16%Z; 17%Z; -3%Z; -19%Z; -20%Z]
    (Some 0%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;14;2;-3;-4;0;5;6;-7;9;10;11;-12;13;14;-15;16;17;-3;-19;-20] = 
     [1;14;2;3;4;0;5;6;7;9;10;11;12;13;14;15;16;17;3;19;20] *)
  (* sum_mags = 1+14+2+3+4+0+5+6+7+9+10+11+12+13+14+15+16+17+3+19+20 = 211 *)
  (* map Z.sgn [1;14;2;-3;-4;0;5;6;-7;9;10;11;-12;13;14;-15;16;17;-3;-19;-20] = 
     [1;1;1;-1;-1;0;1;1;-1;1;1;1;-1;1;1;-1;1;1;-1;-1;-1] *)
  (* prod_sgs = 1 * 1 * 1 * (-1) * (-1) * 0 * 1 * 1 * (-1) * 1 * 1 * 1 * (-1) * 1 * 1 * (-1) * 1 * 1 * (-1) * (-1) * (-1) = 0 *)
  reflexivity.
Qed.