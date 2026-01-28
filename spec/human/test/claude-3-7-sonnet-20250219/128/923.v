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
  problem_128_spec [1%Z; 2%Z; 3%Z; -3%Z; 2%Z; 7%Z; -5%Z; -4%Z; 16%Z; 16%Z] (Some (-59%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;2;3;-3;2;7;-5;-4;16;16] = [1;2;3;3;2;7;5;4;16;16] *)
  (* sum_mags = 1+2+3+3+2+7+5+4+16+16 = 59 *)
  (* map Z.sgn [1;2;3;-3;2;7;-5;-4;16;16] = [1;1;1;-1;1;1;-1;-1;1;1] *)
  (* Count the number of negative signs: -3, -5, -4 => 3 negatives, product is -1 *)
  (* prod_sgs = 1*1*1*(-1)*1*1*(-1)*(-1)*1*1 = -1 *)
  (* output = Some (59 * -1) = Some (-59) *)
  reflexivity.
Qed.