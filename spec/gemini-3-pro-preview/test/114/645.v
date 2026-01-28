Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (x : Z) (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eq_dec h x then 1 else 0) + count_occurrences x t
  end.

Definition solve (l : list Z) : Z :=
  let valid := filter (fun x => Z.eqb (count_occurrences x l) x) l in
  match valid with
  | [] => -1
  | h :: t => fold_right Z.min h t
  end.

Example test_case:
  solve [1; -1; 1; -1; 1; -1; 1; 1; -1; 1; -1; 1; -1; 90; 0; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1] = -1.
Proof.
  vm_compute.
  reflexivity.
Qed.