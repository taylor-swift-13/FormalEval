Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Open Scope string_scope.

Fixpoint strlen (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ s' => S (strlen s')
  end.

Fixpoint strrev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String.append (strrev s') (String c EmptyString)
  end.

Definition palindrome (s : string) : Prop :=
  s = strrev s.

Definition begins_with (pref s : string) : Prop :=
  exists suf, s = String.append pref suf.

Definition is_palindrome_spec (s : string) (b : bool) : Prop :=
  b = true <-> palindrome s.

Definition make_palindrome_spec (s : string) (t : string) : Prop :=
  palindrome t
  /\ begins_with s t
  /\ (forall t', palindrome t' -> begins_with s t' -> strlen t <= strlen t')
  /\ (exists v w,
        s = String.append v w
        /\ palindrome w
        /\ t = String.append s (strrev v)
        /\ (forall v' w',
              s = String.append v' w'
              /\ palindrome w'
              -> strlen v <= strlen v')).

Example test_make_palindrome_raceredder : make_palindrome_spec "raceredder" "raceredderecar".
Proof.
  unfold make_palindrome_spec.
  split.
  - (* 1. palindrome t *)
    unfold palindrome. simpl. reflexivity.
  - split.
    + (* 2. begins_with s t *)
      unfold begins_with. exists "ecar". simpl. reflexivity.
    + split.
      * (* 3. minimality condition *)
        intros t' Hpal Hbeg.
        destruct Hbeg as [suf Heq].
        rewrite Heq. simpl.
        destruct suf as [|c0 suf]; [rewrite Heq in Hpal; simpl in Hpal; try congruence; try (injection Hpal; intros; discriminate) | ].
        destruct suf as [|c1 suf]; [rewrite Heq in Hpal; simpl in Hpal; try congruence; try (injection Hpal; intros; discriminate) | ].
        destruct suf as [|c2 suf]; [rewrite Heq in Hpal; simpl in Hpal; try congruence; try (injection Hpal; intros; discriminate) | ].
        destruct suf as [|c3 suf]; [rewrite Heq in Hpal; simpl in Hpal; try congruence; try (injection Hpal; intros; discriminate) | ].
        simpl. repeat apply le_n_S. apply le_0_n.
      * (* 4. structural decomposition *)
        exists "race", "redder".
        split.
        -- simpl. reflexivity.
        -- split.
           ++ unfold palindrome. simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** intros v' w' [Hsw Hpalw].
                 destruct v' as [|c0 v']; [simpl in Hsw; subst; simpl in Hpalw; try congruence; try (injection Hpalw; intros; discriminate) | ].
                 destruct v' as [|c1 v']; [simpl in Hsw; injection Hsw as Hc Hsw; subst; simpl in Hpalw; try congruence; try (injection Hpalw; intros; discriminate) | ].
                 destruct v' as [|c2 v']; [simpl in Hsw; injection Hsw as Hc Hsw; subst; simpl in Hpalw; try congruence; try (injection Hpalw; intros; discriminate) | ].
                 destruct v' as [|c3 v']; [simpl in Hsw; injection Hsw as Hc Hsw; subst; simpl in Hpalw; try congruence; try (injection Hpalw; intros; discriminate) | ].
                 simpl. repeat apply le_n_S. apply le_0_n.
Qed.