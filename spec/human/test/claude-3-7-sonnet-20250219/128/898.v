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
  problem_128_spec [1%Z; 2%Z; -3%Z; -4%Z; 5%Z; 6%Z; -7%Z; -8%Z; 9%Z; 10%Z; 11%Z; -12%Z; 13%Z; 13%Z; 14%Z; -15%Z; 16%Z; 3%Z; -18%Z; -19%Z; -20%Z] (Some (-209%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* map Z.abs [1;2;-3;-4;5;6;-7;-8;9;10;11;-12;13;13;14;-15;16;3;-18;-19;-20] = *)
  (* [1;2;3;4;5;6;7;8;9;10;11;12;13;13;14;15;16;3;18;19;20] *)
  (* sum_mags = 1+2+3+4+5+6+7+8+9+10+11+12+13+13+14+15+16+3+18+19+20 = 222 *)
  (* map Z.sgn [...] = [1;1;-1;-1;1;1;-1;-1;1;1;1;-1;1;1;1;-1;1;1;-1;-1;-1] *)
  (* prod_sgs = 1*1*(-1)*(-1)*1*1*(-1)*(-1)*1*1*1*(-1)*1*1*1*(-1)*1*1*(-1)*(-1)*(-1) *)
  (* Pairing signs for easier multiplication: *)
  (* (-1)*(-1) = 1, so cancels out at those points *)
  (* After cancellation, multiply remaining signs: *)
  (* Final prod_sgs = -1 *)
  (* output = Some (222 * -1) = Some (-222) *)
  (* But given output = Some (-209%Z) - so let's recheck sum_mags calculation *)

  (* Recalculate sum_mags carefully: *)
  (* 1 + 2 = 3 *)
  (* 3 + 3 = 6 *)
  (* 6 + 4 = 10 *)
  (* 10 + 5 = 15 *)
  (* 15 + 6 = 21 *)
  (* 21 + 7 = 28 *)
  (* 28 + 8 = 36 *)
  (* 36 + 9 = 45 *)
  (* 45 + 10 = 55 *)
  (* 55 + 11 = 66 *)
  (* 66 + 12 = 78 *)
  (* 78 + 13 = 91 *)
  (* 91 + 13 = 104 *)
  (* 104 + 14 = 118 *)
  (* 118 + 15 = 133 *)
  (* 133 + 16 = 149 *)
  (* 149 + 3 = 152 *)
  (* 152 + 18 = 170 *)
  (* 170 + 19 = 189 *)
  (* 189 + 20 = 209 *)

  (* So the sum of magnitudes is 209. *)
  (* Multiplying by prod_sgs = -1 gives Some (-209). *)

  reflexivity.
Qed.