Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition prod_signs_spec (arr : list Z) (output : option Z) : Prop :=
  match arr with
  | [] => output = None
  | _ :: _ =>
    let sum_mags := fold_right Z.add 0 (map Z.abs arr) in
    let prod_sgs := fold_right Z.mul 1 (map Z.sgn arr) in
    output = Some (sum_mags * prod_sgs)
  end.

Example prod_signs_test :
  prod_signs_spec [1%Z; -4%Z; -5%Z] (Some 10%Z).
Proof.
  unfold prod_signs_spec.
  simpl.
  reflexivity.
Qed.