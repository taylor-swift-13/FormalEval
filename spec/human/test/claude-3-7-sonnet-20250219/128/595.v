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
  problem_128_spec [4%Z; 1%Z; 2%Z; 2%Z; 3%Z; -4%Z; -5%Z; 10%Z; 7%Z; 8%Z; 2%Z; -10%Z; -10%Z; 7%Z; -10%Z; -10%Z] (Some 95%Z).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [4;1;2;2;3;-4;-5;10;7;8;2;-10;-10;7;-10;-10] = [4;1;2;2;3;4;5;10;7;8;2;10;10;7;10;10] *)
  (* sum_mags = 4+1+2+2+3+4+5+10+7+8+2+10+10+7+10+10 = 97 *)
  (* map Z.sgn [4;1;2;2;3;-4;-5;10;7;8;2;-10;-10;7;-10;-10] = [1;1;1;1;1;-1;-1;1;1;1;1;-1;-1;1;-1;-1] *)
  (* prod_sgs = 1*1*1*1*1*(-1)*(-1)*1*1*1*1*(-1)*(-1)*1*(-1)*(-1) *)
  (* Count negatives: 6 negatives, so product is 1 *)
  (* output = Some (97 * 1) = Some 97 *)
  (* But expected output is 95, re-check sum *)
  (* sum_mags recalculation: *)
  (* 4 + 1 = 5 *)
  (* 5 + 2 = 7 *)
  (* 7 + 2 = 9 *)
  (* 9 + 3 = 12 *)
  (* 12 + 4 = 16 *)
  (* 16 + 5 = 21 *)
  (* 21 + 10 = 31 *)
  (* 31 + 7 = 38 *)
  (* 38 + 8 = 46 *)
  (* 46 + 2 = 48 *)
  (* 48 + 10 = 58 *)
  (* 58 + 10 = 68 *)
  (* 68 + 7 = 75 *)
  (* 75 + 10 = 85 *)
  (* 85 + 10 = 95 *)
  (* Re-ordered addition confirms sum_mags = 95 *)
  (* Correcting sum_mags to 95 *)
  (* product of signs has 6 negatives, even number, so product is 1 *)
  reflexivity.
Qed.