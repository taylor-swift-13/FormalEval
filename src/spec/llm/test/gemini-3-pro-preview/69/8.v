Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (l : list Z) (x : Z) : Z :=
  match l with
  | [] => 0
  | h :: t => (if Z.eqb h x then 1 else 0) + count_occurrences t x
  end.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => count_occurrences l x >=? x) l in
  match candidates with
  | [] => -1
  | _ => fold_right Z.max (-1) candidates
  end.

Example test_search: search [6; 7; 1; 8; 8; 10; 5; 8; 5; 3; 10] = 1.
Proof.
  compute.
  reflexivity.
Qed.