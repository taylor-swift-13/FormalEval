Here is the full content of the Coq output file, including the inferred specification and the proof for the new test case.

```coq
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_occurrences (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0%nat
  | h :: t => (if Z.eqb x h then 1%nat else 0%nat) + count_occurrences x t
  end.

Fixpoint remove_all (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eqb x h then remove_all x t else h :: remove_all x t
  end.

Fixpoint solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t =>
      match count_occurrences h t with
      | 0%nat => solution t
      | _ => 1 + solution (remove_all h t)
      end
  end.

Example test_case_2: solution [11%Z; 12%Z; 13%Z; 14%Z; 14%Z; 16%Z; 16%Z] = 2%Z.
Proof.
  simpl.
  reflexivity.
Qed.