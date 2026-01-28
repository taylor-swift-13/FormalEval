Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (l : list Z) (x : Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h x then S (count_occ t x) else count_occ t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => Z.geb (Z.of_nat (count_occ l x)) x) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_case: search [1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 2%Z; -1%Z] = -1%Z.
Proof. reflexivity. Qed.