From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition prod_signs (arr : list Z) : option Z :=
  match arr with
  | [] => None
  | _ =>
    let magnitudes := map Z.abs arr in
    let signs := map (fun x => if x =? 0 then 0 else if x <? 0 then -1 else 1) arr in
    Some ((fold_right Z.add 0 magnitudes) * (fold_right Z.mul 1 signs))
  end.

Example test_prod_signs: prod_signs [-10; -2; -8; -7; -6; -5; -4; -3; -9; -2; -1; -2; -1] = Some (-60).
Proof. reflexivity. Qed.