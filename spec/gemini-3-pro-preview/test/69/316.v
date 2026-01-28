Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => (if Z.eq_dec h x then 1%nat else 0%nat) + count x t
  end.

Fixpoint remove_all (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eq_dec h x then remove_all x t else h :: remove_all x t
  end.

Fixpoint distinct (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if (existsb (fun y => Z.eqb h y) t) 
              then distinct t 
              else h :: distinct t
  end.

Definition get_max_freq_elem (l : list Z) : Z :=
  let candidates := distinct l in
  match candidates with
  | [] => 0
  | h :: t => 
      let best := fold_left (fun acc x => 
         if Nat.ltb (count acc l) (count x l) then x else acc
      ) t h in
      best
  end.

Definition solution (l : list Z) : Z :=
  let m := get_max_freq_elem l in
  let l' := remove_all m l in
  get_max_freq_elem l'.

Example test_case: solution [9%Z; 9%Z; 5%Z; 6%Z; 8%Z; 2%Z; 10%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 3%Z; 4%Z; 4%Z; 4%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 8%Z; 1%Z; 1%Z; 1%Z; 1%Z; 6%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] = 4%Z.
Proof.
  compute.
  reflexivity.
Qed.