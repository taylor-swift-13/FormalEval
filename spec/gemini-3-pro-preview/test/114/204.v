Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => (if Z.eq_dec x h then 1%nat else 0%nat) + count x t
  end.

Definition solve (l : list Z) : Z :=
  let unique := nodup Z.eq_dec l in
  match unique with
  | [] => 0
  | h :: t =>
      let res := fold_left (fun (acc : Z * nat) (x : Z) =>
                              let (best_val, min_f) := acc in
                              let f := count x l in
                              if (f <? min_f)%nat then (x, f)
                              else if (f =? min_f)%nat then (Z.min best_val x, min_f)
                              else acc
                           ) t (h, count h l) in
      fst res
  end.

Example test_case: solve [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; 100%Z; 50%Z] = -100%Z.
Proof. reflexivity. Qed.