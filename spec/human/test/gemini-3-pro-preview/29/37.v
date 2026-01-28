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

(* Test case: input = ["zzbb"; "zz"], substring = "a", output = [] *)
Example problem_29_test : problem_29_spec ["zzbb"; "zz"] "a" [].
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
      destruct H_in as [H_zzbb | [H_zz | H_false]].
      * (* Case 1: s = "zzbb" *)
        subst s.
        (* prefix "a" "zzbb" is false *)
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 2: s = "zz" *)
        subst s.
        (* prefix "a" "zz" is false *)
        simpl in H_prefix.
        discriminate H_prefix.
      * (* Case 3: s in [] *)
        contradiction H_false.
Qed.