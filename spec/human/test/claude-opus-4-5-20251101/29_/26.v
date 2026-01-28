Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(*
  子列表定义
*)
Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).


(* Pre: no additional constraints for `filter_by_prefix` by default *)
Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  (* 1. output 是 input 的一个子序列。
        这个自定义的 is_subsequence 保证了：
        - output 中的所有元素都来自 input (规约第一条)
        - output 中元素的相对顺序与 input 中一致 (规约第四条)
  *)
  is_subsequence output input /\

  (* 2. 一个字符串 s 在 output 中，当且仅当它在 input 中且满足前缀条件。
        这蕴含了：
        - output 中的所有元素都满足前缀条件 (规约第二条)
        - input 中所有满足前缀条件的元素都在 output 中 (规约第三条)
  *)
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).

Example test_filter_by_prefix_2 :
  problem_29_spec ["zz"%string; "z"%string] "z"%string ["zz"%string; "z"%string].
Proof.
  unfold problem_29_spec.
  split.
  - (* is_subsequence ["zz"; "z"] ["zz"; "z"] *)
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* forall s, In s ["zz"; "z"] <-> (In s ["zz"; "z"] /\ String.prefix "z" s = true) *)
    intro s.
    split.
    + (* In s ["zz"; "z"] -> ... *)
      intro H.
      simpl in H.
      destruct H as [Hs | [Hs | Hfalse]].
      * (* s = "zz" *)
        subst s.
        split.
        -- simpl. left. reflexivity.
        -- simpl. reflexivity.
      * (* s = "z" *)
        subst s.
        split.
        -- simpl. right. left. reflexivity.
        -- simpl. reflexivity.
      * destruct Hfalse.
    + (* ... -> In s ["zz"; "z"] *)
      intro H.
      destruct H as [Hin Hprefix].
      simpl in Hin.
      destruct Hin as [Hs | [Hs | Hfalse]].
      * (* s = "zz" *)
        subst s.
        simpl. left. reflexivity.
      * (* s = "z" *)
        subst s.
        simpl. right. left. reflexivity.
      * destruct Hfalse.
Qed.