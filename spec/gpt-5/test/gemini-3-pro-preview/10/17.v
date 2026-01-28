Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

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

Example test_make_palindrome_rrefrerace : make_palindrome_spec "rrefrerace" "rrefreracecarerferr".
Proof.
  unfold make_palindrome_spec.
  split.
  - unfold palindrome. simpl. reflexivity.
  - split.
    + unfold begins_with. exists "carerferr"%string. simpl. reflexivity.
    + split.
      * intros t' Hpal Hbeg.
        destruct Hbeg as [u Hu].
        subst t'.
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        destruct u. { simpl in Hpal. discriminate. }
        simpl. repeat apply le_n_S. apply le_0_n.
      * exists "rrefrerac"%string. exists "e"%string.
        split.
        -- simpl. reflexivity.
        -- split.
           ++ unfold palindrome. simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** intros v' w' [H1 H2].
                 destruct v'. { simpl in H1. symmetry in H1. subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { simpl in H1. injection H1; intros; subst. simpl in H2. discriminate. }
                 destruct v'. { 
                   simpl in H1. injection H1; intros; subst. 
                   simpl. apply le_n. 
                 }
                 destruct v'. { 
                   simpl in H1. injection H1; intros; subst. 
                   simpl. apply le_S. apply le_n. 
                 }
                 simpl in H1. discriminate.
Qed.