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
    ["apple"%string; "banana"%string; "orange"%string; "apricot"%string; "kiwi"%string]
    ("a"%string)
    ["apple"%string; "apricot"%string].
Proof.
  unfold problem_29_spec.
  split.
  - simpl.
    left. split; [reflexivity|].
    simpl.
    right.
    simpl.
    right.
    simpl.
    left. split; [reflexivity|].
    simpl. exact I.
  - intros s; split.
    + intros HIn.
      simpl in HIn.
      destruct HIn as [Hs_apple | [Hs_apricot | Hfalse]].
      * subst s.
        split.
        -- simpl. left. reflexivity.
        -- compute. reflexivity.
      * subst s.
        split.
        -- simpl. right. simpl. right. simpl. right. simpl. left. reflexivity.
        -- compute. reflexivity.
      * exfalso. exact Hfalse.
    + intros [Hin Hpref].
      simpl in Hin.
      destruct Hin as [Hs_apple | [Hs_banana | [Hs_orange | [Hs_apricot | [Hs_kiwi | Hin_false]]]]].
      * subst s. simpl. left. reflexivity.
      * subst s. compute in Hpref. discriminate Hpref.
      * subst s. compute in Hpref. discriminate Hpref.
      * subst s. simpl. right. left. reflexivity.
      * subst s. compute in Hpref. discriminate Hpref.
      * exfalso. exact Hin_false.
Qed.