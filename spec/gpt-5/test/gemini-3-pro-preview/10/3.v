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

Example test_make_palindrome_xyz : make_palindrome_spec "xyz" "xyzyx".
Proof.
  unfold make_palindrome_spec.
  split.
  - (* 1. palindrome t *)
    unfold palindrome. simpl. reflexivity.
  - split.
    + (* 2. begins_with s t *)
      unfold begins_with. exists "yx". simpl. reflexivity.
    + split.
      * (* 3. minimality condition *)
        intros t' Hpal Hbeg.
        unfold begins_with in Hbeg. destruct Hbeg as [suf Ht'].
        rewrite Ht'. simpl.
        destruct suf as [|c1 suf1].
        { (* suf = "" *)
          rewrite Ht' in Hpal. simpl in Hpal. inversion Hpal.
        }
        destruct suf1 as [|c2 suf2].
        { (* suf has 1 char *)
          rewrite Ht' in Hpal. simpl in Hpal. inversion Hpal.
        }
        (* suf has >= 2 chars, so len t' >= 5 *)
        simpl. repeat apply le_n_S. apply le_0_n.
      * (* 4. structural decomposition *)
        exists "xy", "z".
        split.
        -- simpl. reflexivity.
        -- split.
           ++ unfold palindrome. simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** (* Minimality of v *)
                 intros v' w' [Happend Hpal].
                 destruct v' as [|c1 v1].
                 { (* v' = "" *)
                   simpl in Happend. subst w'.
                   simpl in Hpal. inversion Hpal.
                 }
                 destruct v1 as [|c2 v2].
                 { (* v' has 1 char *)
                   simpl in Happend. inversion Happend. subst.
                   simpl in Hpal. inversion Hpal.
                 }
                 (* v' has >= 2 chars *)
                 simpl. repeat apply le_n_S. apply le_0_n.
Qed.