Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(*
  子列表定义
*)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(* Pre: no additional constraints for `filter_by_prefix` by default *)
Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  is_subsequence output input /\
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example problem_29_test_case :
  problem_29_spec
    ["a"%string; "ab"%string; "abc"%string; "ba"%string; "bb"%string; "bc"%string]
    ("a"%string)
    ["a"%string; "ab"%string; "abc"%string].
Proof.
  unfold problem_29_spec.
  split.
  - simpl.
    left. split; [reflexivity|].
    simpl.
    left. split; [reflexivity|].
    simpl.
    left. split; [reflexivity|].
    simpl. exact I.
  - intros s; split.
    + intros HIn.
      simpl in HIn.
      destruct HIn as [Hs | [Hs | [Hs | Hfalse]]]; subst.
      * split.
        { simpl. left. reflexivity. }
        { compute. reflexivity. }
      * split.
        { simpl. right. left. reflexivity. }
        { compute. reflexivity. }
      * split.
        { simpl. right. right. left. reflexivity. }
        { compute. reflexivity. }
      * exfalso. exact Hfalse.
    + intros [Hin Hpref].
      simpl in Hin.
      simpl.
      destruct Hin as [Hs | [Hs | [Hs | [Hs | [Hs | [Hs | Hfalse]]]]]]; subst.
      * left. reflexivity.
      * right. left. reflexivity.
      * right. right. left. reflexivity.
      * exfalso. compute in Hpref. discriminate.
      * exfalso. compute in Hpref. discriminate.
      * exfalso. compute in Hpref. discriminate.
      * exfalso. exact Hfalse.
Qed.