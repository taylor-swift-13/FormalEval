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

Example make_palindrome_empty : make_palindrome_spec EmptyString EmptyString.
Proof.
  unfold make_palindrome_spec.
  split.
  - (* palindrome EmptyString *)
    unfold palindrome. simpl. reflexivity.
  - split.
    + (* begins_with EmptyString EmptyString *)
      unfold begins_with. exists EmptyString. simpl. reflexivity.
    + split.
      * (* forall t', palindrome t' -> begins_with EmptyString t' -> strlen EmptyString <= strlen t' *)
        intros t' _ _. simpl. apply Nat.le_0_l.
      * (* exists v w, ... *)
        exists EmptyString. exists EmptyString.
        split.
        -- (* EmptyString = append EmptyString EmptyString *)
           simpl. reflexivity.
        -- split.
           ++ (* palindrome EmptyString *)
              unfold palindrome. simpl. reflexivity.
           ++ split.
              ** (* EmptyString = append EmptyString (strrev EmptyString) *)
                 simpl. reflexivity.
              ** (* forall v' w', ... *)
                 intros v' w' [Heq Hpal].
                 simpl. apply Nat.le_0_l.
Qed.