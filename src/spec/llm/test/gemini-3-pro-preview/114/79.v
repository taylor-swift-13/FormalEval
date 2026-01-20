Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition prod_signs (arr : list Z) : option Z :=
  match arr with
  | [] => None
  | _ =>
    let prod := fold_left (fun acc x => if x =? 0 then 0 else if x <? 0 then -acc else acc) arr 1 in
    let sum := fold_left Z.add arr 0 in
    Some (sum * prod)
  end.

Example example_test_case : prod_signs [-8; -3; -2; -4; 6; -1; -8] = Some (-20).
Proof.
  reflexivity.
Qed.