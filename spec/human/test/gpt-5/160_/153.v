Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.

Inductive find_index_rel {A} (p : A -> bool) : list A -> option nat -> Prop :=
  | fir_nil : find_index_rel p [] None
  | fir_found : forall x xs, p x = true -> find_index_rel p (x :: xs) (Some 0%nat)
  | fir_skip : forall x xs k, p x = false -> find_index_rel p xs (Some k) -> find_index_rel p (x :: xs) (Some (S k))
  | fir_none : forall x xs, p x = false -> find_index_rel p xs None -> find_index_rel p (x :: xs) None.

Inductive rfind_index_rel {A} (p : A -> bool) (l : list A) (res : option nat) : Prop :=
  | rfir_do : forall rev_l rev_res,
      List.rev l = rev_l ->
      find_index_rel p rev_l rev_res ->
      (match rev_res with
       | Some i => res = Some (List.length l - 1 - i)%nat
       | None => res = None
       end) ->
      rfind_index_rel p l res.

Definition is_add_sub (c : ascii) := orb ((c =? "+"%char)%char) ((c =? "-"%char)%char).
Definition is_mul_div (c : ascii) := orb ((c =? "*"%char)%char) ((c =? "/"%char)%char).
Definition is_pow (c : ascii) := ((c =? "^"%char)%char).

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

Example problem_160_example :
  problem_160_spec "^^-++"
    [7%Z; 5%Z; 4%Z; 9%Z; 3%Z; 9%Z]
    1535589058228964592278097181151415909200385800452495618150720642558740272322299488400821914700875797183165562794910089618874549353298389638535468977632311792677723234363039812929990798224753440087824188191010805346435998749996092640979530974424855611373502186548925391038652857840156250967512563069982941255640478823554939640561443613796856865588141056286824186637033949488464663290280364476539987909480558828315138852768523111975503843351865420654483184799794043499337516602578703543161331291559200663108824166410988611631420810%Z.
Proof.
  unfold problem_160_spec.
  eapply er_split with (i := 4%nat) (op := "+"%char).
  - eapply fsir_add_sub with (i := 4%nat).
    + eapply rfir_do with (rev_l := ["+"%char; "+"%char; "-"%char; "^"%char; "^"%char]) (rev_res := Some 0%nat).
      * simpl. reflexivity.
      * apply fir_found. simpl. reflexivity.
      * simpl. reflexivity.
    + reflexivity.
  - simpl. reflexivity.
  - eapply er_split with (i := 3%nat) (op := "+"%char).
    + eapply fsir_add_sub with (i := 3%nat).
      * eapply rfir_do with (rev_l := ["+"%char; "-"%char; "^"%char; "^"%char]) (rev_res := Some 0%nat).
        -- simpl. reflexivity.
        -- apply fir_found. simpl. reflexivity.
        -- simpl. reflexivity.
      * reflexivity.
    + simpl. reflexivity.
    + eapply er_split with (i := 2%nat) (op := "-"%char).
      * eapply fsir_add_sub with (i := 2%nat).
        -- eapply rfir_do with (rev_l := ["-"%char; "^"%char; "^"%char]) (rev_res := Some 0%nat).
           ++ simpl. reflexivity.
           ++ apply fir_found. simpl. reflexivity.
           ++ simpl. reflexivity.
        -- reflexivity.
      * simpl. reflexivity.
      * eapply er_split with (i := 0%nat) (op := "^"%char).
        -- eapply fsir_pow with (res_pow := Some 0%nat).
           ++ eapply rfir_do with (rev_l := ["^"%char; "^"%char]) (rev_res := None).
              ** simpl. reflexivity.
              ** apply fir_none.
                 --- simpl. reflexivity.
                 --- apply fir_none.
                     +++ simpl. reflexivity.
                     +++ apply fir_nil.
              ** simpl. reflexivity.
           ++ eapply rfir_do with (rev_l := ["^"%char; "^"%char]) (rev_res := None).
              ** simpl. reflexivity.
              ** apply fir_none.
                 --- simpl. reflexivity.
                 --- apply fir_none.
                     +++ simpl. reflexivity.
                     +++ apply fir_nil.
              ** simpl. reflexivity.
           ++ apply fir_found. simpl. reflexivity.
           ++ reflexivity.
        -- simpl. reflexivity.
        -- apply er_single.
        -- eapply er_split with (i := 0%nat) (op := "^"%char).
           ++ eapply fsir_pow with (res_pow := Some 0%nat).
              ** eapply rfir_do with (rev_l := ["^"%char]) (rev_res := None).
                 --- simpl. reflexivity.
                 --- apply fir_none. simpl. reflexivity. apply fir_nil.
                 --- simpl. reflexivity.
              ** eapply rfir_do with (rev_l := ["^"%char]) (rev_res := None).
                 --- simpl. reflexivity.
                 --- apply fir_none. simpl. reflexivity. apply fir_nil.
                 --- simpl. reflexivity.
              ** apply fir_found. simpl. reflexivity.
              ** reflexivity.
           ++ simpl. reflexivity.
           ++ apply er_single.
           ++ apply er_single.
           ++ apply ior_pow.
        -- apply ior_pow.
      * apply er_single.
      * apply ior_sub.
    + apply er_single.
    + apply ior_add.
  - apply er_single.
  - apply ior_add.
Qed.