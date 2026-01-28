Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Definition provided in the specification *)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(* Pre-condition definition *)
Definition problem_29_pre (input : list string) : Prop := True.

(* Specification definition *)
Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

(* Test case: input = ["xyz"; "efg"; "hij"], substring = "a", output = [] *)
Example problem_29_test : problem_29_spec ["xyz"; "efg"; "hij"] "a" [].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    (* Since output is [], is_subsequence returns True immediately by definition *)
    simpl.
    trivial.
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward: In s [] -> ... *)
      intros H.
      inversion H. (* False implies anything *)
    + (* Backward: In s input /\ prefix ... -> In s [] *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_xyz | [H_efg | [H_hij | H_false]]].
      * (* Case 1: s = "xyz" *)
        subst s.
        (* prefix "a" "xyz" is false *)
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 2: s = "efg" *)
        subst s.
        (* prefix "a" "efg" is false *)
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 3: s = "hij" *)
        subst s.
        (* prefix "a" "hij" is false *)
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 4: s in [] *)
        contradiction H_false.
Qed.