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

Example test_make_palindrome_onoon : make_palindrome_spec "onoon" "onoono".
Proof.
  unfold make_palindrome_spec.
  split.
  - unfold palindrome. simpl. reflexivity.
  - split.
    + unfold begins_with. exists "o". simpl. reflexivity.
    + split.
      * intros t' Hpal Hbeg.
        destruct Hbeg as [suf Heq].
        rewrite Heq.
        destruct suf.
        -- simpl in *. subst t'.
           unfold palindrome in Hpal. simpl in Hpal.
           congruence.
        -- simpl. repeat apply le_n_S. apply le_0_n.
      * exists "o", "noon".
        split.
        -- simpl. reflexivity.
        -- split.
           ++ unfold palindrome. simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** intros v' w' [Heq Hpal_w].
                 destruct v'.
                 --- simpl in Heq. subst w'.
                     unfold palindrome in Hpal_w. simpl in Hpal_w.
                     congruence.
                 --- simpl. apply le_n_S. apply le_0_n.
Qed.