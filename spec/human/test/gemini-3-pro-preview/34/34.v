Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list string) : Prop := True.

(* Helper for string less-than-or-equal *)
Definition string_le (s1 s2 : string) : Prop := (String.leb s1 s2 = true).

(*
  Spec(input, output) defines "output is the sorted unique version of input"
*)
Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  (* 1. Output list is sorted by string_le *)
  Sorted string_le output /\

  (* 2. Output list has unique elements *)
  NoDup output /\

  (* 3. Input and Output lists contain the same set of elements. *)
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["apple"; "d"; "orange"; "d"] ["apple"; "d"; "orange"].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted string_le output *)
    unfold string_le.
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; reflexivity.
    - apply HdRel_cons; reflexivity.
  }
  split.
  { (* Part 2: NoDup output *)
    repeat apply NoDup_cons.
    (* Prove that head is not in tail for each step *)
    all: try (simpl; intuition; discriminate).
    apply NoDup_nil.
  }
  { (* Part 3: In s input <-> In s output *)
    intro z.
    (* Verify set equivalence by exhaustive check *)
    split; intro H; simpl in *; intuition.
  }
Qed.