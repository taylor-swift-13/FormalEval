Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_elem {A : Type} (lst : list (list A)) (coord : Z * Z) : option A :=
  let (r, c) := coord in
  if orb (r <? 0) (c <? 0) then None
  else
    match nth_error lst (Z.to_nat r) with
    | Some row => nth_error row (Z.to_nat c)
    | None => None
    end.

Inductive coord_order (c1 c2 : Z * Z) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

Inductive is_sorted : list (Z * Z) -> Prop :=
  | sorted_nil : is_sorted []
  | sorted_one : forall c, is_sorted [c]
  | sorted_cons : forall c1 c2 tail,
      coord_order c1 c2 ->
      is_sorted (c2 :: tail) ->
      is_sorted (c1 :: c2 :: tail).

Definition problem_87_spec (lst : list (list Z)) (x : Z) (res : list (Z * Z)) : Prop :=
  (forall coord : Z * Z, In coord res -> get_elem lst coord = Some x) /\
  (forall r c : Z,
    match get_elem lst (r, c) with
    | Some v => v = x -> In (r, c) res
    | None => True
    end) /\
  is_sorted res /\
  NoDup res.

(* Define the example input and output *)

Definition lst_example : list (list Z) :=
  [[1;2;3;4;5;6];
   [1;2;3;4;1;6];
   [1;2;3;4;5;1]].

Definition x_example := 1.

Definition res_example : list (Z * Z) :=
  [(0, 0); (1, 4); (1, 0); (2, 5); (2, 0)].

(* Helpful lemmas about nth_error on lst_example *)

Lemma nth_error_lst_example_0 : nth_error lst_example 0 = Some [1;2;3;4;5;6].
Proof. reflexivity. Qed.

Lemma nth_error_lst_example_1 : nth_error lst_example 1 = Some [1;2;3;4;1;6].
Proof. reflexivity. Qed.

Lemma nth_error_lst_example_2 : nth_error lst_example 2 = Some [1;2;3;4;5;1].
Proof. reflexivity. Qed.

(* Now the inner list nth_error *)

Lemma nth_error_row0_col0 : nth_error [1;2;3;4;5;6] 0 = Some 1.
Proof. reflexivity. Qed.

Lemma nth_error_row1_col0 : nth_error [1;2;3;4;1;6] 0 = Some 1.
Proof. reflexivity. Qed.

Lemma nth_error_row1_col4 : nth_error [1;2;3;4;1;6] 4 = Some 1.
Proof. reflexivity. Qed.

Lemma nth_error_row2_col0 : nth_error [1;2;3;4;5;1] 0 = Some 1.
Proof. reflexivity. Qed.

Lemma nth_error_row2_col5 : nth_error [1;2;3;4;5;1] 5 = Some 1.
Proof. reflexivity. Qed.

Example problem_87_example_proof :
  problem_87_spec lst_example x_example res_example.
Proof.
  unfold problem_87_spec.
  repeat split.

  - (* Correctness: all coords in res_example point to 1 in lst_example *)
    intros coord H_in.
    destruct coord as [r c].
    simpl in *.
    destruct H_in as [H|[H|[H|[H|H]]]]; try (inversion H; clear H).
    + subst r c.
      unfold get_elem; simpl.
      rewrite nth_error_lst_example_0, nth_error_row0_col0.
      reflexivity.
    + subst r c.
      unfold get_elem; simpl.
      rewrite nth_error_lst_example_1, nth_error_row1_col4.
      reflexivity.
    + subst r c.
      unfold get_elem; simpl.
      rewrite nth_error_lst_example_1, nth_error_row1_col0.
      reflexivity.
    + subst r c.
      unfold get_elem; simpl.
      rewrite nth_error_lst_example_2, nth_error_row2_col5.
      reflexivity.
    + subst r c.
      unfold get_elem; simpl.
      rewrite nth_error_lst_example_2, nth_error_row2_col0.
      reflexivity.

  - (* Completeness: all coordinates of value 1 are in res_example *)
    intros r c.
    unfold get_elem.
    destruct (Z.ltb r 0) eqn:Hrlt; destruct (Z.ltb c 0) eqn:Hclt; simpl; try auto.
    destruct (nth_error lst_example (Z.to_nat r)) eqn:Hnth; try auto.
    destruct (nth_error l (Z.to_nat c)) eqn:Hnthc; try auto.
    intros Hval Heq.
    inversion Heq; clear Heq; subst v.
    (* We check all possible coordinates where value = 1 in lst_example *)
    destruct (Z.eq_dec r 0).
    + subst r.
      destruct (Z.eq_dec c 0).
      * subst c. left; reflexivity.
      * (* for other c on row 0, no 1 is present *)
        unfold lst_example in Hnth.
        rewrite Nat2Z.id in Hnth.
        rewrite Hnth in *.
        inversion Hnth; subst l.
        rewrite Hnthc in *.
        (* List row0 = [1;2;3;4;5;6], only col 0 is 1 *)
        destruct (Z.to_nat c) eqn:Hcnat; simpl in *.
        -- (* c=0 handled *)
           lia.
        -- discriminate.
    + destruct (Z.eq_dec r 1).
      * subst r.
        destruct (Z.eq_dec c 4).
        -- subst c. right; left; reflexivity.
        -- destruct (Z.eq_dec c 0).
           ++ subst c. right; right; left; reflexivity.
           ++ unfold lst_example in Hnth.
              rewrite Nat2Z.id in Hnth.
              rewrite Hnth in *.
              inversion Hnth; subst l.
              rewrite Hnthc in *.
              (* Only cols 0 and 4 have value 1 *)
              destruct (Z.to_nat c) eqn:Hcnat; simpl in *.
              --- lia.
              --- discriminate.
      * destruct (Z.eq_dec r 2).
        -- subst r.
           destruct (Z.eq_dec c 5).
           ++ subst c. right; right; right; left; reflexivity.
           ++ destruct (Z.eq_dec c 0).
              ** subst c. right; right; right; right; left; reflexivity.
              ** unfold lst_example in Hnth.
                 rewrite Nat2Z.id in Hnth.
                 rewrite Hnth in *.
                 inversion Hnth; subst l.
                 rewrite Hnthc in *.
                 (* Only cols 0 and 5 have value 1 *)
                 destruct (Z.to_nat c) eqn:Hcnat; simpl in *.
                 --- lia.
                 --- discriminate.
        -- (* r not 0,1,2 implies nth_error None *)
           unfold lst_example in Hnth.
           rewrite Nat2Z.id in Hnth.
           rewrite Hnth in *.
           discriminate.

  - (* is_sorted *)
    apply sorted_cons.
    + apply row_lt. lia.
    + apply sorted_cons.
      * apply col_gt; [reflexivity|lia].
      * apply sorted_cons.
        -- apply row_lt. lia.
        -- apply sorted_cons.
           ++ apply col_gt; [reflexivity|lia].
           ++ apply sorted_cons.
              ** apply row_lt. lia.
              ** apply sorted_one.

  - (* NoDup *)
    unfold res_example.
    repeat constructor; congruence.
Qed.