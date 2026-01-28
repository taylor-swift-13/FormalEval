Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.

Open Scope string_scope.

(* Specification definitions *)
Definition is_substring (part whole : string) : Prop :=
  exists prefix suffix : string, whole = prefix ++ part ++ suffix.

Definition is_rotation (s r : string) : Prop :=
  exists u v : string, s = u ++ v /\ r = v ++ u.

Definition cycpattern_check_spec (a b : string) (res : bool) : Prop :=
  res = true <-> (exists r : string, is_rotation b r /\ is_substring r a).

(* Tactic to solve substring mismatches by exhausting positions *)
Ltac solve_sub Heq :=
  destruct pre; simpl in Heq;
  [ try (inversion Heq; discriminate)
  | destruct pre; simpl in Heq;
    [ try (inversion Heq; discriminate)
    | destruct pre; simpl in Heq;
      [ try (inversion Heq; discriminate)
      | try (inversion Heq; discriminate) ] ] ].

(* Proof for the specific test case *)
Example test_xyzw_xyw : cycpattern_check_spec "xyzw" "xyw" false.
Proof.
  unfold cycpattern_check_spec.
  split.
  - (* -> direction: false = true implies anything *)
    intro H. discriminate H.
  - (* <- direction: contradiction *)
    intro H.
    destruct H as [r [Hrot Hsub]].
    unfold is_rotation in Hrot.
    destruct Hrot as [u [v [Heq1 Heq2]]].
    unfold is_substring in Hsub.
    destruct Hsub as [pre [suf Heq3]].

    (* We analyze the split of "xyw" into u and v *)
    destruct u.
    + (* Case u = "" *)
      simpl in Heq1. subst v. simpl in Heq2. subst r.
      (* r = "xyw" *)
      solve_sub Heq3.
    + inversion Heq1. subst a.
      destruct u.
      * (* Case u = "x" *)
        simpl in Heq1. subst v. simpl in Heq2. subst r.
        (* r = "ywx" *)
        solve_sub Heq3.
      * inversion H1. subst a.
        destruct u.
        -- (* Case u = "xy" *)
           simpl in Heq1. subst v. simpl in Heq2. subst r.
           (* r = "wxy" *)
           solve_sub Heq3.
        -- inversion H0. subst a.
           destruct u.
           ++ (* Case u = "xyw" *)
              simpl in Heq1. subst v. simpl in Heq2. subst r.
              (* r = "xyw" *)
              solve_sub Heq3.
           ++ (* Case u longer than "xyw" *)
              simpl in Heq1. discriminate.
Qed.