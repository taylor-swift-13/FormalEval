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
  problem_29_spec ["aaaajavascript"%string; "aaaa"%string] ("b"%string) [].
Proof.
  unfold problem_29_spec.
  split.
  - simpl. exact I.
  - intros s; split.
    + intros HIn. simpl in HIn. exfalso; exact HIn.
    + intros [Hin Hpref].
      exfalso.
      simpl in Hin.
      destruct Hin as [Hs_first | [Hs_second | Hin_false]].
      * subst. compute in Hpref. discriminate Hpref.
      * subst. compute in Hpref. discriminate Hpref.
      * exact Hin_false.
Qed.