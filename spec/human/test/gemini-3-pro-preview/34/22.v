Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list Z) : Prop := True.

(*
  Spec(input, output) defines "output is the sorted unique version of input"
*)
Definition problem_34_spec (input : list Z) (output : list Z) : Prop :=
  (* 1. Output list is sorted by less-than-or-equal (Z.le) *)
  Sorted Z.le output /\

  (* 2. Output list has unique elements *)
  NoDup output /\

  (* 3. Input and Output lists contain the same set of elements. *)
  (forall z, In z input <-> In z output).

Example test_problem_34 :
  problem_34_spec [1; 1; 1] [1].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted Z.le output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
  }
  split.
  { (* Part 2: NoDup output *)
    repeat apply NoDup_cons.
    all: try (simpl; intuition; lia).
    apply NoDup_nil.
  }
  { (* Part 3: In z input <-> In z output *)
    intro z.
    split; intro H; simpl in *; intuition.
  }
Qed.