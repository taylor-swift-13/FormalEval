(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Specification *)
Definition problem_128_spec (arr : list Z) (output : option Z) : Prop :=
  match arr with
  | [] =>
    output = None
  | _ :: _ =>
    let sum_mags := fold_right Z.add 0 (map Z.abs arr) in
    let prod_sgs := fold_right Z.mul 1 (map Z.sgn arr) in
    output = Some (sum_mags * prod_sgs)
  end.

(* Example proof *)
Example test_prod_signs :
  problem_128_spec [1%Z; 2%Z; 2%Z; -4%Z] (Some (-9%Z)).
Proof.
  unfold problem_128_spec.
  simpl.
  (* Simplify the map and fold_right directly in the goal *)
  simpl.
  (* Compute the sum of magnitudes *)
  assert (sum_mags: fold_right Z.add 0%Z [1%Z; 2%Z; 2%Z; 4%Z] = 9%Z).
  {
    simpl. reflexivity.
  }
  rewrite sum_mags.
  (* Compute the product of signs *)
  assert (prod_sgs: fold_right Z.mul 1%Z [1%Z; 1%Z; 1%Z; -1%Z] = (-1)%Z).
  {
    simpl. reflexivity.
  }
  rewrite prod_sgs.
  (* Compute the final result *)
  simpl.
  reflexivity.
Qed.