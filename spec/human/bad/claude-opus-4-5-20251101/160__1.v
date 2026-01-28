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

(* Test case: operators = "^*+" representing ["**"; "*"; "+"], operands = [2; 3; 4; 5]
   Expression: 2 ^ 3 * 4 + 5 = 8 * 4 + 5 = 32 + 5 = 37 *)

Example test_problem_160 :
  problem_160_spec "^*+" [2%Z; 3%Z; 4%Z; 5%Z] 37%Z.
Proof.
  unfold problem_160_spec.
  simpl.
  (* ops = ["^"; "*"; "+"], nums = [2; 3; 4; 5] *)
  (* Split at index 2 (the "+") - lowest precedence, rightmost *)
  eapply (er_split ["^"%char; "*"%char; "+"%char] [2; 3; 4; 5] 2%nat "+"%char 32 5 37).
  - (* find_split_index_rel ["^"; "*"; "+"] (Some 2) *)
    apply (fsir_add_sub 2%nat).
    + (* rfind_index_rel is_add_sub ["^"; "*"; "+"] (Some 2) *)
      apply (rfir_do _ _ _ ["+"%char; "*"%char; "^"%char] (Some 0%nat)).
      * reflexivity.
      * apply fir_found. reflexivity.
      * simpl. reflexivity.
    + reflexivity.
  - (* op = nth 2 ["^"; "*"; "+"] " " = "+" *)
    reflexivity.
  - (* eval_rel (firstn 2 ["^"; "*"; "+"]) (firstn 3 [2; 3; 4; 5]) 32 *)
    (* eval_rel ["^"; "*"] [2; 3; 4] 32 *)
    simpl.
    (* Split at index 1 (the "*") *)
    eapply (er_split ["^"%char; "*"%char] [2; 3; 4] 1%nat "*"%char 8 4 32).
    + (* find_split_index_rel ["^"; "*"] (Some 1) *)
      apply (fsir_mul_div 1%nat).
      * (* rfind_index_rel is_add_sub ["^"; "*"] None *)
        apply (rfir_do _ _ _ ["*"%char; "^"%char] None).
        -- reflexivity.
        -- apply fir_none. reflexivity.
           apply fir_none. reflexivity.
           apply fir_nil.
        -- reflexivity.
      * (* rfind_index_rel is_mul_div ["^"; "*"] (Some 1) *)
        apply (rfir_do _ _ _ ["*"%char; "^"%char] (Some 0%nat)).
        -- reflexivity.
        -- apply fir_found. reflexivity.
        -- simpl. reflexivity.
      * reflexivity.
    + reflexivity.
    + (* eval_rel (firstn 1 ["^"; "*"]) (firstn 2 [2; 3; 4]) 8 *)
      (* eval_rel ["^"] [2; 3] 8 *)
      simpl.
      eapply (er_split ["^"%char] [2; 3] 0%nat "^"%char 2 3 8).
      * (* find_split_index_rel ["^"] (Some 0) *)
        apply (fsir_pow (Some 0%nat)).
        -- apply (rfir_do _ _ _ ["^"%char] None).
           ++ reflexivity.
           ++ apply fir_none. reflexivity. apply fir_nil.
           ++ reflexivity.
        -- apply (rfir_do _ _ _ ["^"%char] None).
           ++ reflexivity.
           ++ apply fir_none. reflexivity. apply fir_nil.
           ++ reflexivity.
        -- apply fir_found. reflexivity.
        -- reflexivity.
      * reflexivity.
      * simpl. apply er_single.
      * simpl. apply er_single.
      * (* interp_op_rel "^" 2 3 8 *)
        replace 8 with (Z.pow 2 3) by reflexivity.
        apply ior_pow.
    + (* eval_rel (skipn 2 ["^"; "*"]) (skipn 2 [2; 3; 4]) 4 *)
      (* eval_rel [] [4] 4 *)
      simpl. apply er_single.
    + (* interp_op_rel "*" 8 4 32 *)
      replace 32 with (8 * 4) by reflexivity.
      apply ior_mul.
  - (* eval_rel (skipn 3 ["^"; "*"; "+"]) (skipn 3 [2; 3; 4; 5]) 5 *)
    (* eval_rel [] [5] 5 *)
    simpl. apply er_single.
  - (* interp_op_rel "+" 32 5 37 *)
    replace 37 with (32 + 5) by reflexivity.
    apply ior_add.
Qed.