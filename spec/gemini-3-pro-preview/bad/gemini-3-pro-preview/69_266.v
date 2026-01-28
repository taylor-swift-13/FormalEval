Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occ (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occ x t
  end.

Fixpoint remove_all (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eqb h x then remove_all x t else h :: remove_all x t
  end.

Fixpoint unique (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => h :: unique (remove_all h t)
  end.

Definition solve (l : list Z) : Z :=
  let u := unique l in
  let counts := map (fun x => count_occ x l) u in
  let evens := filter Nat.even counts in
  Z.of_nat (length evens).

Example test_case: solve [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 18%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z; 1%Z] = 3%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.