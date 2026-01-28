Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list bool) : Prop := True.

(* Define an ordering for booleans where false <= true *)
Definition bool_le (b1 b2 : bool) : Prop := implb b1 b2 = true.

(*
  Spec(input, output) defines "output is the sorted unique version of input"
*)
Definition problem_34_spec (input : list bool) (output : list bool) : Prop :=
  (* 1. Output list is sorted by bool_le *)
  Sorted bool_le output /\

  (* 2. Output list has unique elements *)
  NoDup output /\

  (* 3. Input and Output lists contain the same set of elements. *)
  (forall z, In z input <-> In z output).

Example test_problem_34 :
  problem_34_spec [true; true; false; false; true; true] [false; true].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted bool_le output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons. simpl. reflexivity.
  }
  split.
  { (* Part 2: NoDup output *)
    repeat apply NoDup_cons.
    - simpl. intuition; discriminate.
    - simpl. intuition.
    - apply NoDup_nil.
  }
  { (* Part 3: In z input <-> In z output *)
    intro z.
    split; intro H; simpl in *; intuition.
  }
Qed.