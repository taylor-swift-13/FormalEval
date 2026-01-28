Looking at the error, the issue is that `find_index_rel` is used in the definition of `rfind_index_rel` but hasn't been defined yet. I need to fix the order of definitions and provide a complete working proof.

```coq
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.

(* 辅助函数：查找满足条件的第一个元素的索引 *)
Inductive find_index_rel {A} (p : A -> bool) : list A -> option nat -> Prop :=
  | fir_nil : find_index_rel p [] None
  | fir_found : forall x xs, p x = true -> find_index_rel p (x :: xs) (Some 0%nat)
  | fir_skip : forall x xs k, p x = false -> find_index_rel p xs (Some k) -> find_index_rel p (x :: xs) (Some (S k))
  | fir_none : forall x xs, p x = false -> find_index_rel p xs None -> find_index_rel p (x :: xs) None.

(* 辅助函数：查找满足条件的最后一个元素的索引 *)
Inductive rfind_index_rel {A} (p : A -> bool) (l : list A) (res : option nat) : Prop :=
  | rfir_do : forall rev_l rev_res,
      rev l = rev_l ->
      find_index_rel p rev_l rev_res ->
      (match rev_res with
       | Some i => res = Some (List.length l - 1 - i)%nat
       | None => res = None
       end) ->
      rfind_index_rel p l res.

Definition is_add_sub (c : ascii) := orb (c =? "+"%char)%char (c =? "-"%char)%char.
Definition is_mul_div (c : ascii) := orb (c =? "*"%char)%char (c =? "/"%char)%char.
Definition is_pow (c : ascii) := (c =? "^"%char)%char.

(* 确定分割表达式的操作符索引：优先级 +,- < *,/ < ^ *)
Inductive find_split_index_rel (ops : list ascii) (res : option nat) : Prop :=
  | fsir_add_sub : forall i,
      rfind_index_rel is_add_sub ops (Some i) ->
      res = Some i ->
      find_split_index_rel ops res
  | fsir_mul_div : forall i,
      rfind_index_rel is_add_sub ops None ->
      rfind_index_rel is_mul_div ops (Some i) ->
      res = Some i ->
      find_split_index_rel ops res
  | fsir_pow : forall res_pow,
      rfind_index_rel is_add_sub ops None ->
      rfind_index_rel is_mul_div ops None ->
      find_index_rel is_pow ops res_pow ->
      res = res_pow ->
      find_split_index_rel ops res.

Inductive interp_op_rel : ascii -> Z -> Z -> Z -> Prop :=
  | ior_add : forall z1 z2, interp_op_rel "+"%char z1 z2 (z1 + z2)
  | ior_sub : forall z1 z2, interp_op_rel "-"%char z1 z2 (z1 - z2)
  | ior_mul : forall z1 z2, interp_op_rel "*"%char z1 z2 (z1 * z2)
  | ior_div : forall z1 z2, z2 <> 0 -> interp_op_rel "/"%char z1 z2 (Z.div z1 z2)
  | ior_pow : forall z1 z2, interp_op_rel "^"%char z1 z2 (Z.pow z1 z2).

Inductive eval_rel : list ascii -> list Z -> Z -> Prop :=
  | er_single : forall n, eval_rel [] [n] n
  | er_split : forall ops nums i op v1 v2 v,
      find_split_index_rel ops (Some i) ->
      op = nth i ops " "%char ->
      eval_rel (firstn i ops) (firstn (i + 1) nums) v1 ->
      eval_rel (skipn (i + 1) ops) (skipn (i + 1) nums) v2 ->
      interp_op_rel op v1 v2 v ->
      eval_rel ops nums v.

Definition problem_160_pre (operators : string) (operands : list Z) : Prop :=
  let ops := list_ascii_of_string operators in
  S (List.length ops) = List.length operands /\
  (1 <= List.length ops)%nat /\ (2 <= List.length operands)%nat /\
  Forall (fun z => 0 <= z) operands /\
  Forall (fun c => c = "+"%char \/ c = "-"%char \/ c = "*"%char \/ c = "/"%char \/ c = "^"%char) ops.

Definition problem_160_spec (operators : string) (operands : list Z) (result : Z) : Prop :=
  eval_rel (list_ascii_of_string operators) operands result.

(* Helper lemmas for list operations *)
Lemma firstn_singleton : forall A (x:A) n, firstn 1 (x::n) = [x].
Proof. intros. simpl. reflexivity. Qed.

Lemma skipn_singleton : forall A (x:A) n, skipn 1 (x::n) = n.
Proof. intros. simpl. reflexivity. Qed.

Lemma firstn_2 : forall A (x y:A) xs, firstn 2 (x::y::xs) = [x; y].
Proof. intros. simpl. reflexivity. Qed.

Lemma skipn_2 : forall A (x y:A) xs, skipn 2 (x::y::xs) = xs.
Proof. intros. simpl. reflexivity. Qed.

Lemma find_index_rel_const : forall A (p:A->bool) x,
    p x = true -> find_index_rel p (x::nil) (Some 0).
Proof.
  intros. apply fir_found. assumption.
Qed.

Lemma rfind_index_rel_singleton_true : forall A p (x:A),
    p x = true -> rfind_index_rel p [x] (Some 0).
Proof.
  intros. eapply rfir_do.
  - reflexivity.
  - eapply fir_found. exact H.
  - simpl. reflexivity.
Qed.

Lemma rfind_index_rel_singleton_false : forall A p (x:A),
    p x = false -> rfind_index_rel p [x] None.
Proof.
  intros. eapply rfir_do.
  - reflexivity.
  - eapply fir_none.
    + exact H.
    + apply fir_nil.
  - reflexivity.
Qed.

Lemma find_split_index_rel_single : forall op,
    find_split_index_rel [op] (Some 0).
Proof.
  intros.
  destruct (is_add_sub op) eqn:Haddsub.
  - apply fsir_add_sub with (i:=0).
    + apply rfind_index_rel_singleton_true. exact Haddsub.
    + reflexivity.
  - destruct (is_mul_div op) eqn:Hmuldiv.
    * apply fsir_mul_div with (i:=0).
      + apply rfind_index_rel_singleton_false. exact Haddsub.
      + apply rfind_index_rel_singleton_true. exact Hmuldiv.
      + reflexivity.
    * apply fsir_pow with (res_pow:=Some 0).
      + apply rfind_index_rel_singleton_false. exact Haddsub.
      + apply rfind_index_rel_singleton_false. exact Hmuldiv.
      + apply find_index_rel_const.
        unfold is_pow. destruct op; reflexivity.
      + reflexivity.
Qed.

Lemma find_split_index_rel_second : forall op1 op2,
    find_split_index_rel [op1; op2] (Some 1).
Proof.
  intros.
  destruct (is_add_sub op2) eqn:Haddsub2.
  - apply fsir_add_sub with (i:=1).
    + eapply rfir_do.
      * reflexivity.
      * simpl. apply fir_skip.
        { destruct (is_add_sub op1) eqn:Haddsub1; auto. }
        apply fir_found. exact Haddsub2.
      * simpl. reflexivity.
    + reflexivity.
  - destruct (is_mul_div op2) eqn:Hmuldiv2.
    * apply fsir_mul_div with (i:=1).
      + eapply rfir_do.
        * reflexivity.
        * simpl. apply fir_skip.
          { destruct (is_add_sub op1) eqn:Haddsub1; auto. }
          apply fir_none.
          { exact Haddsub2. }
          apply fir_nil.
        * reflexivity.
      + eapply rfir_do.
        * reflexivity.
        * simpl. apply fir_skip.
          { destruct (is_mul_div op1) eqn:Hmuldiv1; auto. }
          apply fir_found. exact Hmuldiv2.
        * simpl. reflexivity.
      + reflexivity.
    * apply fsir_pow with (res_pow:=Some 1).
      + eapply rfir_do.
        * reflexivity.
        * simpl. apply fir_skip.
          { destruct (is_add_sub op1) eqn:Haddsub1; auto. }
          apply fir_none.
          { exact Haddsub2. }
          apply fir_nil.
        * reflexivity.
      + eapply rfir_do.
        * reflexivity.
        * simpl. apply fir_skip.
          { destruct (is_mul_div op1) eqn:Hmuldiv1; auto. }
          apply fir_none.
          { exact Hmuldiv2. }
          apply fir_nil.
        * reflexivity.
      + simpl. apply fir_skip.
        { unfold is_pow. destruct op1; reflexivity. }
        apply fir_found. unfold is_pow. destruct op2; reflexivity.
      + reflexivity.
Qed.

Lemma interp_op_rel_example1 : interp_op_rel "^"%char 2 3 8.
Proof. apply ior_pow. Qed.

Lemma interp_op_rel_example2 : interp_op_rel "*"%char 8 4 32.
Proof. apply ior_mul. Qed.

Lemma interp_op_rel_example3 : interp_op_rel "+"%char 32 5 37.
Proof. apply ior_add. Qed.

Lemma eval_rel_single : forall n, eval_rel [] [n] n.
Proof. apply er_single. Qed.

Example example_proof : problem_160_spec "**+*+"%string [2;3;4;5] 37.
Proof.
  unfold problem_160_spec.
  simpl list_ascii_of_string.
  
  (* Build the expression: (2 ** 3) * 4 + 5 = 37 *)
  apply er_split with (i:=2) (op:="+"%char) (v1:=32) (v2:=5).
  - apply find_split_index_rel_second.
  - reflexivity.
  - (* Prove left subexpression: (2 ** 3) * 4 = 32 *)
    apply er_split with (i:=1) (op:="*"%char) (v1:=8) (v2:=4).
    + apply find_split_index_rel_second.
    + reflexivity.
    + (* Prove left sub-subexpression: 2 ** 3 = 8 *)
      apply er_split with (i:=0) (op:="^"%char) (v1:=2) (v2:=3).
      * apply find_split_index_rel_single.
      * reflexivity.
      * apply eval_rel_single.
      * apply eval_rel_single.
      * apply interp_op_rel_example1.
    + (* Prove right sub-subexpression: 4 = 4 *)
      apply eval_rel_single.
    + (* Prove multiplication: 8 * 4 = 32 *)
      apply interp_op_rel_example2.
  - (* Prove right subexpression: 5 = 5 *)
    apply eval_rel_single.
  - (* Prove addition: 32 + 5 = 37 *)
    apply interp_op_rel_example3.
Qed.