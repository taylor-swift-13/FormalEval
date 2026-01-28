Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* Helper function to compare strings lexicographically *)
Fixpoint string_leb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, _ => true
  | String _ _, EmptyString => false
  | String c1 s1', String c2 s2' =>
      if (nat_of_ascii c1 <? nat_of_ascii c2)%nat then true
      else if (nat_of_ascii c2 <? nat_of_ascii c1)%nat then false
      else string_leb s1' s2'
  end.

Definition string_le (s1 s2 : string) : Prop := string_leb s1 s2 = true.

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
  problem_34_spec ["apple"; "banana"; "orange"] ["apple"; "banana"; "orange"].
Proof.
  unfold problem_34_spec.
  split.
  { (* Part 1: Sorted string_le output *)
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons. compute. reflexivity.
    - apply HdRel_cons. compute. reflexivity.
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