Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  let negs := filter (fun x => x <? 0) l in
  match negs with
  | [] => 1
  | _ => fold_right Z.add 0 negs
  end.

Example test_case: solve [-10; -9; -7; -6; -3; -70; -2; -1; -5; -7] = -120.
Proof.
  reflexivity.
Qed.