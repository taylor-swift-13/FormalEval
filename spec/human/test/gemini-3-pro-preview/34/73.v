Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.NArith.NArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope string_scope.

(* Helper for string comparison *)
Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      let n1 := N_of_ascii c1 in
      let n2 := N_of_ascii c2 in
      if (n1 <? n2)%N then True
      else if (n2 <? n1)%N then False
      else string_le s1' s2'
  end.

(* Pre: no additional constraints for `unique` by default *)
Definition problem_34_pre (input : list string) : Prop := True.

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
  problem_34_spec ["apple"; "banana"; "banaorangcena"; "d"; "orange"] ["apple"; "banana"; "banaorangcena"; "d"; "orange"].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted string_le output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons; simpl; auto.
    - apply HdRel_cons; simpl; auto.
    - apply HdRel_cons; simpl; auto.
    - apply HdRel_cons; simpl; auto.
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
    (* Verify set equivalence by exhaustive check *)
    split; intro H; simpl in *; intuition.
  }
Qed.