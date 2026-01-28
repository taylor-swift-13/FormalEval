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

Example test_make_palindrome_rradar : make_palindrome_spec "rradar" "rradarr".
Proof.
  unfold make_palindrome_spec.
  split.
  - unfold palindrome. simpl. reflexivity.
  - split.
    + unfold begins_with. exists "r". simpl. reflexivity.
    + split.
      * intros t' Hpal Hbeg.
        unfold begins_with in Hbeg.
        destruct Hbeg as [suf Heq].
        rewrite Heq.
        destruct suf.
        -- rewrite Heq in Hpal.
           unfold palindrome in Hpal. simpl in Hpal.
           discriminate Hpal.
        -- simpl.
           do 7 apply le_n_S.
           apply le_0_n.
      * exists "r", "radar".
        split.
        -- simpl. reflexivity.
        -- split.
           ++ unfold palindrome. simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** intros v' w' [Heq Hpalw].
                 destruct v'.
                 --- simpl in Heq. subst w'.
                     unfold palindrome in Hpalw. simpl in Hpalw.
                     discriminate Hpalw.
                 --- simpl. apply le_n_S. apply le_0_n.
Qed.