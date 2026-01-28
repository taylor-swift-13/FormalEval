Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.Init.Nat.
Import ListNotations.

Open Scope R_scope.

Definition problem_4_pre (l : list R) : Prop := l <> [].

Definition problem_4_spec (l : list R) (mad : R) : Prop :=
  let n := length l in
  let mu := fold_right Rplus 0 l / INR n in
  mad = fold_right (fun x acc => acc + Rabs (x - mu)) 0 l / INR n.

Example problem_4_test : problem_4_spec [0; 0; 0; 5; 0; 5.7682420395965925] (2 * (5 + 5.7682420395965925) / 9).
Proof.
  unfold problem_4_spec.
  set (l := [0; 0; 0; 5; 0; 5.7682420395965925]).
  set (mu := (5 + 5.7682420395965925) / 6).
  replace (fold_right Rplus 0 l / INR (length l)) with mu.
  - unfold l. simpl.
    replace (Rabs (0 - mu)) with mu by (rewrite Rabs_left; subst mu; lra).
    replace (Rabs (5 - mu)) with (5 - mu) by (rewrite Rabs_right; subst mu; lra).
    replace (Rabs (5.7682420395965925 - mu)) with (5.7682420395965925 - mu) by (rewrite Rabs_right; subst mu; lra).
    subst mu. lra.
  - subst mu. unfold l. simpl. lra.
Qed.