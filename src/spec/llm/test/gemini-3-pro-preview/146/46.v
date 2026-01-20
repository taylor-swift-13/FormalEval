Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition move_one_ball (arr : list Z) : Z :=
  match arr with
  | [] => 1
  | _ =>
    let rotated := (tl arr) ++ [hd 0 arr] in
    let pairs := combine arr rotated in
    let descents := filter (fun p => (fst p) >? (snd p)) pairs in
    if Z.of_nat (length descents) <=? 1 then 1 else 0
  end.

Example check: move_one_ball [14; -8; 62; 5; 6; -76; 6] = 0.
Proof.
  compute.
  reflexivity.
Qed.