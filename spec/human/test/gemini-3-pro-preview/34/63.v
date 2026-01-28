Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list string) : Prop := True.

(* Helper relation for sorting strings *)
Definition string_le (s1 s2 : string) : Prop :=
  match String.compare s1 s2 with
  | Gt => False
  | _ => True
  end.

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
  problem_34_spec 
    ["orappleange"; "apple"; "banana"; "lQd"; "llQd"; "orange"; "banana"; "banana"] 
    ["apple"; "banana"; "lQd"; "llQd"; "orange"; "orappleange"].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted output *)
    repeat constructor.
    (* Verify ordering for each adjacent pair *)
    all: simpl; try (exact I).
  }
  split.
  { (* Part 2: NoDup output *)
    repeat constructor.
    (* Verify no duplicates *)
    all: simpl; intro H; intuition; discriminate.
  }
  { (* Part 3: Set equivalence *)
    intro z.
    split; intro H; simpl in *; intuition; subst; simpl; auto 10.
  }
Qed.