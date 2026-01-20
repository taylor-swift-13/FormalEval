Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Specification definition inferred from the test case *)
(* Function that computes the sum of squares of elements in a list *)
Definition solution (l : list Z) : Z :=
  fold_right (fun x acc => x * x + acc) 0 l.

(* Test case: input = [25%Z], output = 625%Z *)
Example test_case : solution [25] = 625.
Proof.
  unfold solution.
  simpl.
  reflexivity.
Qed.