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

Example test_make_palindrome_race : make_palindrome_spec "race" "racecar".
Proof.
  unfold make_palindrome_spec.
  split.
  - unfold palindrome. simpl. reflexivity.
  - split.
    + unfold begins_with. exists "car". simpl. reflexivity.
    + split.
      * intros t' Hpal Hbeg.
        destruct Hbeg as [suf Heq].
        subst t'.
        destruct suf.
        { simpl in Hpal. discriminate. }
        destruct suf.
        { simpl in Hpal. injection Hpal. intros. discriminate. }
        destruct suf.
        { simpl in Hpal. injection Hpal. intros. discriminate. }
        simpl. repeat apply le_n_S. apply le_0_n.
      * exists "rac", "e".
        split.
        -- simpl. reflexivity.
        -- split.
           ++ unfold palindrome. simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** intros v' w' [Heq Hpalw].
                 destruct v'.
                 { simpl in Heq. subst w'. simpl in Hpalw. discriminate. }
                 destruct v'.
                 { simpl in Heq. injection Heq as H1 H2. subst. simpl in Hpalw. discriminate. }
                 destruct v'.
                 { simpl in Heq. injection Heq as H1 H2 H3. subst. simpl in Hpalw. discriminate. }
                 simpl. repeat apply le_n_S. apply le_0_n.
Qed.