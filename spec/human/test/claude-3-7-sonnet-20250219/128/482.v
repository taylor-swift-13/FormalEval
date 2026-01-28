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
  problem_128_spec [1%Z; -6%Z; -4%Z; 0%Z; 5%Z; 6%Z; -7%Z; 9%Z; 10%Z; 11%Z; -12%Z; 13%Z; 14%Z; -15%Z; 16%Z; 17%Z; -18%Z; -8%Z; -20%Z; -2%Z; 9%Z; 2%Z; -4%Z] (Some 0%Z).
Proof.
  unfold problem_128_spec.
  simpl.

  (* Compute sum of absolute values *)
  (* map Z.abs [1;-6;-4;0;5;6;-7;9;10;11;-12;13;14;-15;16;17;-18;-8;-20;-2;9;2;-4]
     = [1;6;4;0;5;6;7;9;10;11;12;13;14;15;16;17;18;8;20;2;9;2;4] *)
  (* sum_mags = 1 + 6 + 4 + 0 + 5 + 6 + 7 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 8 + 20 + 2 + 9 + 2 + 4
               = 216 *)

  (* Compute product of signs *)
  (* map Z.sgn [1;-6;-4;0;5;6;-7;9;10;11;-12;13;14;-15;16;17;-18;-8;-20;-2;9;2;-4]
     = [1;-1;-1;0;1;1;-1;1;1;1;-1;1;1;-1;1;1;-1;-1;-1;-1;1;1;-1] *)
  (* product of sgns = 1 * (-1) * (-1) * 0 * 1 * 1 * (-1) * 1 * 1 * 1 * (-1) * 1 * 1 * (-1) * 1 * 1 * (-1) * (-1) * (-1) * (-1) * 1 * 1 * (-1)
                     = 0 because of multiplication by 0 *)

  reflexivity.
Qed.