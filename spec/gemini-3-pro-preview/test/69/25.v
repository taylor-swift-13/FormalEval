Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (l : list Z) (x : Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => if Z.eq_dec h x then S (count t x) else count t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => x <=? Z.of_nat (count l x)) l in
  match candidates with
  | [] => -1
  | h :: t => fold_right Z.max h t
  end.

Example test_search: search [3; 10; 10; 9; 2] = -1.
Proof.
  reflexivity.
Qed.