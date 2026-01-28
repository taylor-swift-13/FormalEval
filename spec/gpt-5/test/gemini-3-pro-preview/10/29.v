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

Example test_make_palindrome_levevltenet : make_palindrome_spec "levevltenet" "levevltenetlvevel".
Proof.
  unfold make_palindrome_spec.
  split.
  - (* 1. palindrome t *)
    unfold palindrome. vm_compute. reflexivity.
  - split.
    + (* 2. begins_with s t *)
      unfold begins_with. exists "lvevel". vm_compute. reflexivity.
    + split.
      * (* 3. minimality condition *)
        intros t' Hpal Hbeg.
        destruct Hbeg as [suf Heq].
        subst t'.
        (* We need to show strlen t <= strlen (s ++ suf).
           strlen t = 17. strlen s = 11.
           So we need 17 <= 11 + strlen suf <-> 6 <= strlen suf. *)
        do 6 (destruct suf; [ unfold palindrome in Hpal; vm_compute in Hpal; discriminate | ]).
        simpl. repeat apply le_n_S. apply le_0_n.
      * (* 4. structural decomposition *)
        exists "levevl", "tenet".
        split.
        -- (* s = v ++ w *)
           vm_compute. reflexivity.
        -- split.
           ++ (* palindrome w *)
              unfold palindrome. vm_compute. reflexivity.
           ++ split.
              ** (* t = s ++ strrev v *)
                 vm_compute. reflexivity.
              ** (* minimality of v *)
                 intros v' w' [H1 H2].
                 (* We need strlen v <= strlen v'.
                    strlen v = 6.
                    So we need 6 <= strlen v'. *)
                 do 6 (destruct v'; [ 
                   simpl in H1; inversion H1; subst w'; 
                   unfold palindrome in H2; vm_compute in H2; discriminate 
                 | ]).
                 simpl. repeat apply le_n_S. apply le_0_n.
Qed.