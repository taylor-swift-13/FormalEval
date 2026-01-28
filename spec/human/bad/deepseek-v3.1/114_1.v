Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition list_sum (l : list Z) : Z :=
  fold_left Z.add l 0.

Definition problem_114_pre (nums : list Z) : Prop := nums <> [].

Definition problem_114_spec (nums : list Z) (min_sum : Z) : Prop :=
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    list_sum sub_array = min_sum)
  /\
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    min_sum <= list_sum sub_array).

Lemma fold_left_add_ge : forall l a,
  a <= fold_left Z.add l a.
Proof.
  induction l; intros; simpl.
  - lia.
  - apply Z.le_trans with (m := a + a0).
    + lia.
    + apply IHl.
Qed.

Lemma in_app_iff3 : forall A (x : A) prefix sub suffix,
  In x (prefix ++ sub ++ suffix) <-> 
  In x prefix \/ In x sub \/ In x suffix.
Proof.
  intros. rewrite in_app_iff. rewrite in_app_iff. tauto.
Qed.

Lemma test_case_114 : 
  problem_114_spec [2%Z; 3%Z; 4%Z; 1%Z; 2%Z; 4%Z] 1%Z.
Proof.
  unfold problem_114_spec.
  split.
  - (* Existence part *)
    exists [1%Z].
    repeat split.
    + discriminate.
    + exists [2%Z; 3%Z; 4%Z], [2%Z; 4%Z].
      reflexivity.
    + unfold list_sum. reflexivity.
  - (* Minimality part *)
    intros sub_array Hnot_empty [prefix [suffix Heq]].
    unfold list_sum.
    
    (* All elements in original list are >= 1 *)
    assert (Hpos: forall x, In x [2%Z; 3%Z; 4%Z; 1%Z; 2%Z; 4%Z] -> 1 <= x).
    { intros x Hin. 
      repeat (destruct Hin as [H|H]; try (subst x; lia)).
      contradiction. }
    
    (* All elements in sub_array are from original list *)
    assert (Hsub_in: forall x, In x sub_array -> In x [2%Z; 3%Z; 4%Z; 1%Z; 2%Z; 4%Z]).
    { intros x Hin.
      rewrite Heq.
      apply in_app_iff3.
      repeat (apply or_introl || apply or_intror).
      exact Hin. }
    
    (* Therefore all elements in sub_array are >= 1 *)
    assert (Hsub_pos: forall x, In x sub_array -> 1 <= x) by auto.
    
    (* Prove sum >= 1 by induction *)
    destruct sub_array as [|x l] eqn:Hsub.
    + contradiction Hnot_empty. reflexivity.
    + simpl.
      (* Base: x >= 1 *)
      assert (Hx_pos: 1 <= x) by (apply Hsub_pos; left; reflexivity).
      
      (* Inductive step: show fold_left Z.add l x >= x >= 1 *)
      apply Z.le_trans with (m := x).
      * lia.
      * apply fold_left_add_ge.
Qed.