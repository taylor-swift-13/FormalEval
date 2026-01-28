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

(* Test case: input = ["xyz"; "efg"; "hij"; "hij"], substring = "aaaajavascript", output = [] *)
Example problem_29_test : problem_29_spec ["xyz"; "efg"; "hij"; "hij"] "aaaajavascript" [].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    trivial.
  - (* Part 2: forall s, In s output <-> In s input /\ prefix substring s = true *)
    intros s.
    split.
    + (* Forward: In s [] -> ... *)
      intros H.
      inversion H.
    + (* Backward: In s input /\ prefix ... -> In s [] *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | H5]]]].
      * (* Case 1: s = "xyz" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 2: s = "efg" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 3: s = "hij" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 4: s = "hij" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 5: s in [] *)
        contradiction H5.
Qed.