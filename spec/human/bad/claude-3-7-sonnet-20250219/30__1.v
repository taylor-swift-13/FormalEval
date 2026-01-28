Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Definition of subsequence *)
Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

(* Predicate for positivity *)
Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_get_positive :
  let input := [-1; -2; 4; 5; 6] in
  let output := [4; 5; 6] in
  problem_30_spec input output.
Proof.
  unfold problem_30_spec.
  split.
  - (* output is subsequence of input *)
    simpl.
    (* construct the subsequence proof *)
    (* input = [-1; -2; 4; 5; 6] *)
    (* output = [4; 5; 6] *)
    apply sub_cons_skip. (* skip -1 *)
    apply sub_cons_skip. (* skip -2 *)
    apply sub_cons_match. (* 4 *)
    apply sub_cons_match. (* 5 *)
    apply sub_cons_match. (* 6 *)
    apply sub_nil.
  - (* forall r, In r output <-> (In r input /\ r > 0) *)
    intros r.
    split.
    + (* -> direction *)
      intros Hin.
      simpl in Hin.
      destruct Hin as [H | [H | [H | H]]].
      * subst r. split.
        { right. right. right. left. reflexivity. }
        { lra. }
      * subst r. split.
        { right. right. right. right. left. reflexivity. }
        { lra. }
      * subst r. split.
        { right. right. left. reflexivity. }
        { lra. }
      * subst r. split.
        { right. left. reflexivity. }
        { lra. }
    + (* <- direction *)
      intros [[Hin | [Hin | [Hin | Hin]]] Hpos].
      * (* r=-1 *)
        lra.
      * (* r=-2 *)
        lra.
      * (* r=4 *)
        left. reflexivity.
      * (* r=5 *)
        right. left. reflexivity.
      * (* r=6 *)
        right. right. left. reflexivity.
Qed.