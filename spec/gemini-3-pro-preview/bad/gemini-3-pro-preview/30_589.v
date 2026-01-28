Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

(* Helper to define the specification using a boolean predicate *)
Definition Rgt_bool (x y : R) : bool :=
  if Rgt_dec x y then true else false.

Definition get_positive_spec (l : list R) (res : list R) : Prop :=
  res = filter (fun x => Rgt_bool x 0) l.

(* Lemmas to help with the proof *)
Lemma Rgt_bool_true : forall x, x > 0 -> Rgt_bool x 0 = true.
Proof.
  intros. unfold Rgt_bool. destruct (Rgt_dec x 0); auto.
  exfalso. apply n. assumption.
Qed.

Lemma Rgt_bool_false : forall x, x <= 0 -> Rgt_bool x 0 = false.
Proof.
  intros. unfold Rgt_bool. destruct (Rgt_dec x 0); auto.
  exfalso. apply Rlt_not_le in r. contradiction.
Qed.

Lemma filter_cons_true : forall A (f : A -> bool) x l, f x = true -> filter f (x::l) = x :: filter f l.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma filter_cons_false : forall A (f : A -> bool) x l, f x = false -> filter f (x::l) = filter f l.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Example test_get_positive : get_positive_spec [-2.25; -4; 2.5; 5; -8; -4; -7; -11.18889279027017; -10.5; 2.5; -11.18889279027017] [2.5; 5; 2.5].
Proof.
  unfold get_positive_spec.
  
  (* -2.25 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le. 
       replace (-2.25) with (- (225/100)) by field.
       apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }

  (* -4 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le.
       apply Ropp_lt_gt_0_contravar. apply IZR_lt. reflexivity. }

  (* 2.5 *)
  rewrite filter_cons_true.
  2: { apply Rgt_bool_true. replace 2.5 with (25/10) by field.
       apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }

  (* 5 *)
  rewrite filter_cons_true.
  2: { apply Rgt_bool_true. apply IZR_lt. reflexivity. }

  (* -8 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le. apply Ropp_lt_gt_0_contravar. apply IZR_lt. reflexivity. }

  (* -4 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le. apply Ropp_lt_gt_0_contravar. apply IZR_lt. reflexivity. }

  (* -7 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le. apply Ropp_lt_gt_0_contravar. apply IZR_lt. reflexivity. }

  (* -11.18889279027017 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le.
       replace (-11.18889279027017) with (- (1118889279027017/100000000000000)) by field.
       apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }

  (* -10.5 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le. replace (-10.5) with (-(105/10)) by field.
       apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }

  (* 2.5 *)
  rewrite filter_cons_true.
  2: { apply Rgt_bool_true. replace 2.5 with (25/10) by field.
       apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }

  (* -11.18889279027017 *)
  rewrite filter_cons_false.
  2: { apply Rgt_bool_false. apply Rlt_le.
       replace (-11.18889279027017) with (- (1118889279027017/100000000000000)) by field.
       apply Ropp_lt_gt_0_contravar. apply Rdiv_lt_0_compat; apply IZR_lt; reflexivity. }

  simpl.
  reflexivity.
Qed.