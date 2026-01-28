Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.

(* Helper function to convert string to list of ascii characters *)
Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* Helper function: Find the index of the first element satisfying predicate p *)
Inductive find_index_rel {A} (p : A -> bool) : list A -> option nat -> Prop :=
  | fir_nil : find_index_rel p [] None
  | fir_found : forall x xs, p x = true -> find_index_rel p (x :: xs) (Some 0%nat)
  | fir_skip : forall x xs k, p x = false -> find_index_rel p xs (Some k) -> find_index_rel p (x :: xs) (Some (S k))
  | fir_none : forall x xs, p x = false -> find_index_rel p xs None -> find_index_rel p (x :: xs) None.

(* Helper function: Find the index of the last element satisfying predicate p *)
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

(* Determine split index based on operator precedence: +,- < *,/ < ^ *)
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

(* Test case: 
   input = [["**"; "*"; "+"]; [2; 3; 4; 5]], output = 37
   Represented as operators="^*+" and operands=[2; 3; 4; 5].
   Evaluation: 2^3 * 4 + 5 = 8 * 4 + 5 = 32 + 5 = 37.
*)
Example test_problem_160 : problem_160_spec "^*+" [2; 3; 4; 5] 37.
Proof.
  unfold problem_160_spec.
  simpl list_ascii_of_string.

  (* Step 1: Split at '+' (index 2) *)
  (* Expression: (2^3*4) + 5 *)
  eapply er_split with (i:=2%nat) (op:="+"%char) (v1:=32) (v2:=5).
  - (* Prove we split at index 2 (the '+') *)
    apply fsir_add_sub.
    eapply rfir_do.
    + reflexivity. (* rev [^; *; +] = [+; *; ^] *)
    + simpl. apply fir_found. reflexivity. (* Found + at head *)
    + reflexivity. (* index = 3 - 1 - 0 = 2 *)
    + reflexivity.
  - reflexivity.
  - (* Left branch: evaluate 2^3*4 to 32 *)
    simpl firstn. simpl skipn.
    (* Step 2: Split at '*' (index 1) *)
    (* Expression: (2^3) * 4 *)
    eapply er_split with (i:=1%nat) (op:="*"%char) (v1:=8) (v2:=4).
    + (* Prove we split at index 1 (the '*') *)
      apply fsir_mul_div.
      * (* No add/sub *)
        eapply rfir_do. reflexivity. simpl. 
        apply fir_none. reflexivity. 
        apply fir_none. reflexivity. 
        apply fir_nil. reflexivity.
      * (* Found * *)
        eapply rfir_do. reflexivity. simpl. 
        apply fir_found. reflexivity. 
        reflexivity. (* index = 2 - 1 - 0 = 1 *)
      * reflexivity.
    + reflexivity.
    + (* Left branch: evaluate 2^3 to 8 *)
      simpl firstn. simpl skipn.
      (* Step 3: Split at '^' (index 0) *)
      eapply er_split with (i:=0%nat) (op:="^"%char) (v1:=2) (v2:=3).
      * (* Prove we split at index 0 (the '^') *)
        apply fsir_pow.
        -- (* No add/sub *)
           eapply rfir_do. reflexivity. simpl. apply fir_none. reflexivity. apply fir_nil. reflexivity.
        -- (* No mul/div *)
           eapply rfir_do. reflexivity. simpl. apply fir_none. reflexivity. apply fir_nil. reflexivity.
        -- (* Found ^ *)
           simpl. apply fir_found. reflexivity.
        -- reflexivity.
      * reflexivity.
      * simpl. apply er_single. (* 2 *)
      * simpl. apply er_single. (* 3 *)
      * apply ior_pow. (* 2^3 = 8 *)
    + (* Right branch of *: 4 *)
      simpl. apply er_single.
    + apply ior_mul. (* 8 * 4 = 32 *)
  - (* Right branch of +: 5 *)
    simpl. apply er_single.
  - apply ior_add. (* 32 + 5 = 37 *)
Qed.