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

(* Test case: input = ["world"; "heworldlo"; "house"], substring = "h", output = ["heworldlo"; "house"] *)
Example problem_29_test : problem_29_spec ["world"; "heworldlo"; "house"] "h" ["heworldlo"; "house"].
Proof.
  unfold problem_29_spec.
  split.
  - (* Part 1: is_subsequence output input *)
    simpl.
    right. (* skip "world" *)
    left. split. reflexivity. (* match "heworldlo" *)
    left. split. reflexivity. (* match "house" *)
    simpl. trivial.
  - (* Part 2: filter property *)
    intros s.
    split.
    + (* Forward: In output -> In input /\ prefix *)
      intros H.
      simpl in H.
      destruct H as [H_he | [H_ho | H_false]].
      * subst s. split.
        -- simpl. right. left. reflexivity.
        -- simpl. reflexivity.
      * subst s. split.
        -- simpl. right. right. left. reflexivity.
        -- simpl. reflexivity.
      * contradiction.
    + (* Backward: In input /\ prefix -> In output *)
      intros [H_in H_prefix].
      simpl in H_in.
      destruct H_in as [H_world | [H_he | [H_ho | H_false]]].
      * (* s = "world" *)
        subst s.
        simpl in H_prefix.
        discriminate H_prefix.
      * (* s = "heworldlo" *)
        subst s.
        simpl. left. reflexivity.
      * (* s = "house" *)
        subst s.
        simpl. right. left. reflexivity.
      * contradiction.
Qed.