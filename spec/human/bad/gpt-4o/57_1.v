Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Open Scope Z_scope.

(* Pre: no special constraints for `monotonic` on integer lists *)
Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

(* Define the monotonic function *)
Fixpoint monotonic_increasing (l: list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _ as xs) =>
    if Z.leb x y then
      monotonic_increasing xs
    else false
  end.

Fixpoint monotonic_decreasing (l: list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: (y :: _ as xs) =>
    if Z.leb y x then
      monotonic_decreasing xs
    else false
  end.

Definition monotonic (l: list Z) : bool :=
  monotonic_increasing l || monotonic_decreasing l.

(* Prove the test case *)
Example problem_57_test_case :
  problem_57_spec [1%Z; 2%Z; 4%Z; 10%Z] true.
Proof.
  unfold problem_57_spec. simpl. split.
  - intros _. left. repeat constructor; lia.
  - intros [Hsorted | Hsorted].
    + reflexivity.
    + inversion Hsorted.
Qed.

Close Scope Z_scope.