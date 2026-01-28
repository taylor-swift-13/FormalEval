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

Example test_make_palindrome_empty : make_palindrome_spec EmptyString EmptyString.
Proof.
  unfold make_palindrome_spec.
  split.
  - (* 1. palindrome t *)
    unfold palindrome. simpl. reflexivity.
  - split.
    + (* 2. begins_with s t *)
      unfold begins_with. exists EmptyString. simpl. reflexivity.
    + split.
      * (* 3. minimality condition *)
        intros t' Hpal Hbeg.
        simpl.
        apply le_0_n.
      * (* 4. structural decomposition *)
        exists EmptyString. exists EmptyString.
        split.
        -- (* s = v ++ w *)
           simpl. reflexivity.
        -- split.
           ++ (* palindrome w *)
              unfold palindrome. simpl. reflexivity.
           ++ split.
              ** (* t = s ++ strrev v *)
                 simpl. reflexivity.
              ** (* minimality of v *)
                 intros v' w' H.
                 simpl.
                 apply le_0_n.
Qed.