Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list R) : Prop := True.

(*
  Spec(input, output) defines "output is the sorted unique version of input"
*)
Definition problem_34_spec (input : list R) (output : list R) : Prop :=
  (* 1. Output list is sorted by less-than-or-equal (Rle) *)
  Sorted Rle output /\

  (* 2. Output list has unique elements *)
  NoDup output /\

  (* 3. Input and Output lists contain the same set of elements. *)
  (forall z, In z input <-> In z output).

Example test_problem_34 :
  problem_34_spec [1.1; 2.2; 3.3; 4.4; 4.4; 4.4] [1.1; 2.2; 3.3; 4.4].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted Rle output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; lra.
    - apply HdRel_cons; lra.
    - apply HdRel_cons; lra.
  }
  split.
  { (* Part 2: NoDup output *)
    repeat apply NoDup_cons.
    (* Prove that head is not in tail for each step *)
    all: try (simpl; intuition; lra).
    apply NoDup_nil.
  }
  { (* Part 3: In z input <-> In z output *)
    intro z.
    (* Verify set equivalence by exhaustive check *)
    split; intro H; simpl in *; intuition.
  }
Qed.