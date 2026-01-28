Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition move_one_ball (arr : list Z) : Z :=
  match arr with
  | [] => 1
  | x :: xs =>
    let rotated := xs ++ [x] in
    let pairs := combine arr rotated in
    let drops := filter (fun p => (fst p) >? (snd p)) pairs in
    if (Z.of_nat (length drops)) <=? 1 then 1 else 0
  end.

Example test_move_one_ball: move_one_ball [100; 101; 102; 102] = 1.
Proof.
  reflexivity.
Qed.