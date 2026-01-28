Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Provide ascii_eqb since it is missing *)
Definition ascii_eqb (a b : ascii) : bool :=
  if ascii_dec a b then true else false.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Inductive find_index_rel {A} (p : A -> bool) : list A -> option nat -> Prop :=
  | fir_nil : find_index_rel p [] None
  | fir_found : forall x xs, p x = true -> find_index_rel p (x :: xs) (Some 0%nat)
  | fir_skip : forall x xs k, p x = false -> find_index_rel p xs (Some k) -> find_index_rel p (x :: xs) (Some (S k))
  | fir_none : forall x xs, p x = false -> find_index_rel p xs None -> find_index_rel p (x :: xs) None.

Inductive rfind_index_rel {A} (p : A -> bool) (l : list A) (res : option nat) : Prop :=
  | rfir_do : forall rev_l rev_res,
      rev l = rev_l ->
      find_index_rel p rev_l rev_res ->
      (match rev_res with
       | Some i => res = Some (List.length l - 1 - i)%nat
       | None => res = None
       end) ->
      rfind_index_rel p l res.

Definition is_add_sub (c : ascii) := orb (ascii_eqb c "+"%char) (ascii_eqb c "-"%char).
Definition is_mul_div (c : ascii) := orb (ascii_eqb c "*"%char) (ascii_eqb c "/"%char).
Definition is_pow (c : ascii) := ascii_eqb c "^"%char.

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

(* Convert string operator list (like ["**"; "*"; "+"]) to ascii operator list *)
Fixpoint ops_of_list (l : list string) : list ascii :=
  match l with
  | [] => []
  | op :: rest =>
    match op with
    | "**" => "^"%char :: ops_of_list rest
    | "*" => "*"%char :: ops_of_list rest
    | "+" => "+"%char :: ops_of_list rest
    | "-" => "-"%char :: ops_of_list rest
    | "//" => "/"%char :: ops_of_list rest
    | _ => " "%char :: ops_of_list rest (* invalid fallback *)
    end
  end.

Example test_case_eval :
  eval_rel
    (ops_of_list ["**"; "*"; "+"])
    [2;3;4;5]
    37.
Proof.
  simpl.
  (* ops_of_list ["**"; "*"; "+"] = ["^"; "*"; "+"] *)

  (* Find split index i = 2 for '+' *)
  assert (Hsplit: find_split_index_rel ["^"; "*"; "+"] (Some 2)).
  {
    apply fsir_add_sub.
    apply rfir_do with (rev_l := ["+"; "*"; "^"]) (rev_res := Some 0).
    - simpl. reflexivity.
    - constructor.
      unfold is_add_sub. simpl.
      rewrite ascii_eqb.
      destruct (ascii_dec "+" "+").
      + reflexivity.
      + contradiction n; reflexivity.
    - simpl. lia.
  }

  eapply er_split with (i:=2) (v1:= ((2 ^ 3) * 4)) (v2:=5) (op:= "+"%char).
  - exact Hsplit.
  - simpl. reflexivity.

  - (* eval_rel ["^"; "*"] [2;3;4] ((2^3)*4) *)

    assert (Hsplit_2: find_split_index_rel ["^"; "*"] (Some 1)).
    {
      apply fsir_mul_div.
      - (* no add_sub *)
        apply rfir_do with (rev_l := ["*"; "^"]) (rev_res := None).
        + simpl. reflexivity.
        + constructor.
        + reflexivity.
      - (* rfind_index_rel is_mul_div *) 
        apply rfir_do with (rev_l := ["*"; "^"]) (rev_res := Some 0).
        + simpl. reflexivity.
        + constructor.
          unfold is_mul_div. simpl.
          rewrite ascii_eqb.
          destruct (ascii_dec "*" "*").
          * reflexivity.
          * contradiction n; reflexivity.
        + simpl. lia.
    }

    eapply er_split with (i:=1) (v1:= (2 ^ 3)) (v2:=4) (op:= "*"%char).
    + exact Hsplit_2.
    + simpl. reflexivity.

    + (* eval_rel ["^"] [2;3] (2^3) *)
      assert (Hsplit_1: find_split_index_rel ["^"] (Some 0)).
      {
        apply fsir_pow.
        - apply rfir_do with (rev_l := ["^"]) (rev_res := None).
          + simpl. reflexivity.
          + constructor.
          + reflexivity.
        - apply rfir_do with (rev_l := ["^"]) (rev_res := None).
          + simpl. reflexivity.
          + constructor.
          + reflexivity.
        - constructor.
          simpl.
          unfold is_pow.
          rewrite ascii_eqb.
          destruct (ascii_dec "^" "^").
          * reflexivity.
          * contradiction n; reflexivity.
        - reflexivity.
      }

      eapply er_split with (i:=0) (v1:=2) (v2:=3) (op:= "^"%char).
      * exact Hsplit_1.
      * simpl. reflexivity.
      * constructor.
      * constructor.
      * apply ior_pow.

    + apply ior_mul.

  - (* eval_rel [] [5] 5 *)
    constructor.

  - (* interp_op_rel "+" ((2^3)*4) 5 37 *)
    simpl.
    assert (Hpow: Z.pow 2 3 = 8) by reflexivity.
    rewrite Hpow.
    assert (Hmul: 8 * 4 = 32) by reflexivity.
    rewrite Hmul.
    simpl.
    apply ior_add.
Qed.