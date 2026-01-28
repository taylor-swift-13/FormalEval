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
  problem_128_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; -6%Z; -7%Z; -8%Z; -9%Z; 1%Z; -10%Z; -10%Z] (Some 66%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;2;3;4;5;-6;-7;-8;-9;1;-10;-10] = [1;2;3;4;5;6;7;8;9;1;10;10] *)
  (* sum_mags = 1+2+3+4+5+6+7+8+9+1+10+10 = 66 *)
  (* map Z.sgn [1;2;3;4;5;-6;-7;-8;-9;1;-10;-10] = [1;1;1;1;1;-1;-1;-1;-1;1;-1;-1] *)
  (* Count of negative signs: 7 negatives, so product of signs = (-1)^7 = -1 *)
  (* Actually, counting negatives: -6, -7, -8, -9, -10, -10: that’s 6 negatives plus one more? *)
  (* Let's count carefully: negatives are at positions 6,7,8,9,11,12 (indices 1-based) => 6 negatives *)
  (* The elements: [1;2;3;4;5;-6;-7;-8;-9;1;-10;-10] *)
  (* Negatives: -6, -7, -8, -9, -10, -10 = 6 negatives => product of signs = (-1)^6 = 1 *)
  (* output = Some (66 * 1) = Some 66 *)
  reflexivity.
Qed.