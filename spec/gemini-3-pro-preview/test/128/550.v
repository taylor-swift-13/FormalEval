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

Example test_prod_signs : prod_signs_spec [1; 2; -3; -8; -4; 0; 5; 6; -7; 9; 10; -19; 6; 11; -12; 13; 14; -15; 16; 17; -18; -8; -20; 9; 2; -4; 16; -15] (Some 0).
Proof.
  unfold prod_signs_spec.
  simpl.
  reflexivity.
Qed.