Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_68_pre (arr : list nat) : Prop := True.

Definition problem_68_spec (arr : list nat) (output : list nat) : Prop :=
  match output with
  | [] =>
    forall val, In val arr -> Nat.even val = false
  | [v; i] =>
    i < length arr /\ nth i arr 0 = v /\
    Nat.even v = true /\
    (forall val, In val arr -> Nat.even val = true -> v <= val) /\
    (forall j, j < i -> nth j arr 0 <> v)
  | _ => False
  end.

Definition pluck (arr : list nat) : list nat :=
  let evens := filter Nat.even arr in
  match evens with
  | [] => []
  | _ =>
    let min_even := fold_right Nat.min (hd 0 evens) evens in
    let index := find (fun x => Nat.even x && Nat.eqb x min_even) arr in
    match index with
    | Some i => [nth i arr 0; i]
    | None => []
    end
  end.

Example pluck_test_1 : pluck [4; 2; 3] = [2; 1].
Proof.
  unfold pluck.
  simpl.
  reflexivity.
Qed.

Example pluck_test_2 : pluck [1; 2; 3] = [2; 1].
Proof.
  unfold pluck.
  simpl.
  reflexivity.
Qed.

Example pluck_test_3 : pluck [] = [].
Proof.
  unfold pluck.
  simpl.
  reflexivity.
Qed.

Example pluck_test_4 : pluck [5; 0; 3; 0; 4; 2] = [0; 1].
Proof.
  unfold pluck.
  simpl.
  reflexivity.
Qed.

Theorem pluck_correct : forall arr,
  problem_68_spec arr (pluck arr).
Proof.
  intros arr.
  unfold problem_68_spec, pluck.
  remember (filter Nat.even arr) as evens.
  destruct evens as [| min_even evens_rest].
  - simpl. intros val Hval. rewrite <- Heqevens in Hval.
    apply filter_In in Hval. destruct Hval as [_ Hfalse].
    now rewrite Nat.even_spec in Hfalse.
  - simpl.
    assert (In min_even (filter Nat.even arr)) as Hmin.
    { rewrite <- Heqevens. simpl. left. reflexivity. }
    pose proof (proj1 (filter_In Nat.even arr min_even) Hmin) as HminIn.
    destruct (find (fun x => Nat.even x && Nat.eqb x (fold_right Nat.min min_even evens_rest)) arr) eqn:Hfind.
    + split.
      * apply find_some in Hfind. destruct Hfind as [HIn Hcond].
        apply andb_true_iff in Hcond. destruct Hcond as [Heven Hmin_eq].
        now apply Nat.eqb_eq in Hmin_eq.
      * split.
        -- apply find_some in Hfind. destruct Hfind as [HIn _].
           now apply nth_In.
        -- split.
           ++ apply find_some in Hfind. destruct Hfind as [_ Hcond].
              apply andb_true_iff in Hcond. destruct Hcond as [Heven _].
              now apply Nat.even_spec.
           ++ split.
              ** intros val Hval Heven_val.
                 rewrite <- Heqevens in Hval.
                 apply filter_In in Hval. destruct Hval as [_ Heven_val'].
                 pose proof (fold_right_min Nat.min min_even evens_rest val).
                 lia.
              ** intros j Hj.
                 apply find_none with (x := nth j arr 0) in Hfind.
                 --- apply Nat.eqb_neq. intros Heq.
                     rewrite Heq in Hfind. apply andb_false_iff in Hfind.
                     destruct Hfind as [Heven_false | Hneq_false].
                     +++ now rewrite Nat.even_spec in Heven_false.
                     +++ now apply Nat.eqb_neq in Hneq_false.
                 --- apply nth_In. lia.
    + exfalso. apply find_none in Hfind.
      ++ rewrite <- Heqevens in Hmin.
         apply filter_In in Hmin. destruct Hmin as [HminIn _].
         apply Hfind in HminIn.
         apply andb_false_iff in HminIn. destruct HminIn as [Hfalse | Hfalse].
         -- now rewrite Nat.even_spec in Hfalse.
         -- apply Nat.eqb_neq in Hfalse.
            pose proof (fold_right_min Nat.min min_even evens_rest min_even).
            lia.
      ++ apply nth_In. lia.
Qed.