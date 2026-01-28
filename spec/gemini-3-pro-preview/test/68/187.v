Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_even_helper (l : list Z) (idx : Z) (best : option (Z * Z)) : option (Z * Z) :=
  match l with
  | [] => best
  | h :: t =>
    let new_best := 
      if Z.even h then
        match best with
        | None => Some (h, idx)
        | Some (val, best_idx) => 
            if h <? val then Some (h, idx) else best
        end
      else best
    in
    find_min_even_helper t (idx + 1) new_best
  end.

Definition solution (l : list Z) : list Z :=
  match find_min_even_helper l 0 None with
  | Some (val, idx) => [val; idx]
  | None => []
  end.

Example test_case: solution [7; 9; 1; 5; 10000; 3; 13; 15; 19; 20; 21; 0; 25; 27; 29; 9; 31; 35; 37; 39; 4; 2; 9] = [0; 11].
Proof.
  vm_compute.
  reflexivity.
Qed.