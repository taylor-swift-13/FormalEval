Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Local Open Scope Z_scope.

Definition count (x : Z) (l : list Z) : Z :=
  fold_right (fun n acc => if Z.eqb n x then acc + 1 else acc) 0 l.

Definition search (l : list Z) : Z :=
  let candidates := filter (fun x => (x >? 0) && (count x l >=? x)) l in
  fold_right Z.max (-1) candidates.

Example test_search: search [1; 2; 2; 2; 2; 2; 2]%Z = 2%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.