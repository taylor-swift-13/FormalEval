Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition prod_signs_spec (arr : list Z) (res : option Z) : Prop :=
  match arr with
  | [] => res = None
  | _ =>
      let sum_magnitudes := fold_right (fun x acc => Z.abs x + acc) 0 arr in
      let prod_signs := fold_right (fun x acc => Z.sgn x * acc) 1 arr in
      res = Some (sum_magnitudes * prod_signs)
  end.

Example test_prod_signs : prod_signs_spec [1%Z; 2%Z; -3%Z; -4%Z; 0%Z; 5%Z; 6%Z; -7%Z; -8%Z; 9%Z; 10%Z; 11%Z; -12%Z; 13%Z; 14%Z; -15%Z; 16%Z; -15%Z; 17%Z; -18%Z; -19%Z; -20%Z; 0%Z] (Some 0%Z).
Proof.
  unfold prod_signs_spec.
  simpl.
  reflexivity.
Qed.