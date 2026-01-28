Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (x y : bool) : Prop :=
  match x, y with
  | true, false => False
  | _, _ => True
  end.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list bool) : Prop := True.

(*
  Spec(input, output) defines "output is the sorted unique version of input"
*)
Definition problem_34_spec (input : list bool) (output : list bool) : Prop :=
  (* 1. Output list is sorted by less-than-or-equal (bool_le) *)
  Sorted bool_le output /\

  (* 2. Output list has unique elements *)
  NoDup output /\

  (* 3. Input and Output lists contain the same set of elements. *)
  (forall b, In b input <-> In b output).

Example test_problem_34 :
  problem_34_spec [false; false; true; true] [false; true].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted bool_le output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons. simpl. trivial.
  }
  split.
  { (* Part 2: NoDup output *)
    repeat apply NoDup_cons.
    (* Prove that head is not in tail for each step *)
    all: try (simpl; intuition; discriminate).
    apply NoDup_nil.
  }
  { (* Part 3: In b input <-> In b output *)
    intro b.
    (* Verify set equivalence by exhaustive check *)
    split; intro H; simpl in *; intuition.
  }
Qed.