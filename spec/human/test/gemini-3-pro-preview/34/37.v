Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list string) : Prop := True.

(*
  Spec(input, output) defines "output is the sorted unique version of input"
*)
Definition problem_34_spec (input : list string) (output : list string) : Prop :=
  (* 1. Output list is sorted by less-than-or-equal (String.leb) *)
  Sorted (fun s1 s2 => String.leb s1 s2 = true) output /\

  (* 2. Output list has unique elements *)
  NoDup output /\

  (* 3. Input and Output lists contain the same set of elements. *)
  (forall s, In s input <-> In s output).

Example test_problem_34 :
  problem_34_spec ["apple"; "banana"; "lQd"; "llQd"; "orange"] ["apple"; "banana"; "lQd"; "llQd"; "orange"].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; simpl; reflexivity.
    - apply HdRel_cons; simpl; reflexivity.
    - apply HdRel_cons; simpl; reflexivity.
    - apply HdRel_cons; simpl; reflexivity.
  }
  split.
  { (* Part 2: NoDup output *)
    repeat apply NoDup_cons.
    (* Prove that head is not in tail for each step *)
    all: try (simpl; intuition; discriminate).
    apply NoDup_nil.
  }
  { (* Part 3: In s input <-> In s output *)
    intro s.
    (* Verify set equivalence *)
    split; intro H; exact H.
  }
Qed.