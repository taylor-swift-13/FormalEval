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
  problem_29_spec ["hello"%string; "world"%string; "heworldlo"%string; "house"%string] ("h"%string) ["hello"%string; "heworldlo"%string; "house"%string].
Proof.
  unfold problem_29_spec.
  split.
  - simpl. left. split.
    + reflexivity.
    + simpl. right.
      simpl. left. split.
      * reflexivity.
      * simpl. left. split.
        { reflexivity. }
        { simpl. exact I. }
  - intros s; split.
    + intros HIn.
      split.
      * simpl in HIn.
        destruct HIn as [Hs_hello | [Hs_heworldlo | [Hs_house | Hfalse]]].
        { subst. simpl. left. reflexivity. }
        { subst. simpl. right. right. left. reflexivity. }
        { subst. simpl. right. right. right. left. reflexivity. }
        { exfalso. exact Hfalse. }
      * simpl in HIn.
        destruct HIn as [Hs_hello | [Hs_heworldlo | [Hs_house | Hfalse]]].
        { subst. compute. reflexivity. }
        { subst. compute. reflexivity. }
        { subst. compute. reflexivity. }
        { exfalso. exact Hfalse. }
    + intros [Hin Hpref].
      simpl in Hin.
      destruct Hin as [Hs_hello | [Hs_world | [Hs_heworldlo | [Hs_house | Hfalse]]]].
      * subst. simpl. left. reflexivity.
      * subst. exfalso. compute in Hpref. discriminate Hpref.
      * subst. simpl. right. left. reflexivity.
      * subst. simpl. right. right. left. reflexivity.
      * exfalso. exact Hfalse.
Qed.